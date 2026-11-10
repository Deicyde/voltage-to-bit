#!/usr/bin/env python3
"""Scan the Lean library sources for constructs that can bypass the kernel or
change how later text is elaborated.

Usage:
    python3 scripts/lean_scan.py [--lakefile lakefile.toml] PATH...

Each PATH is a `.lean` file or a directory searched recursively for `.lean`
files. Exit status: 0 nothing found, 1 at least one finding, 2 usage error.

What this is: a tripwire over the source text. Comments are removed first, by
the same rules as Lean's own lexer (`--` to the end of the line; `/- ... -/`
nesting; `/--` and `/-!` documentation blocks), so prose that mentions a
keyword is not flagged and code hidden behind a comment-like trick is.

What this is not: a proof that the sources contain nothing harmful. It is a
deny-list of known constructs plus three allow-lists (how a command may
start, which modules may be imported, what `lakefile.toml` may contain). It
does not parse Lean: a construct that is on no list is not seen. The checks
that do not depend on a list are the axiom audit and the kernel replay in
`scripts/check.sh`.

Rules.

1. Lexical. Outside comments the sources must not contain a double quote or
   an escaped identifier `«...»`, and every comment must be opened after a
   space or at the start of a line. Each of these would let text that Lean
   reads as code look like a comment to this scan (for example `x <--y` is
   `x <- -y` to Lean), so they are refused instead of interpreted.
2. Deny-list (whole words anywhere in code): see `FORBIDDEN_WORDS`. Also
   `@[` (an attribute), `#` followed by a letter (a command such as `#eval`
   that runs code or stops elaboration), and `+native`.
3. Commands. The library is written with every command starting in column 0.
   So (a) a line that starts in column 0 must start with one of
   `ALLOWED_COMMAND_STARTS`: a command of another kind, for instance one of
   Mathlib's many macro commands, is reported even though no deny-list names
   it; and (b) each of those words, wherever it occurs in code, must stand at
   the start of a line in column 0, or after nothing but the modifiers
   `COMMAND_MODIFIERS` that do. Without (b) an indented command, or a second
   command on the same line, would escape (a) and rules 4 and 5.
4. `variable` commands must not bind an instance-implicit argument `[...]`.
   Lean adds such a variable to later theorems whose text does not mention it.
5. Imports must be modules of Mathlib or of the library itself.
6. `lakefile.toml` (with `--lakefile`) may contain only the lines listed in
   `LAKEFILE_RULES`: compiler options given there apply to every file and
   could switch off the kernel check without any trace in the sources.

`open` and `open scoped` are allowed and are reported as an inventory, because
they bring Mathlib's names and notation into scope and a reader should know
which.

When the library legitimately needs something this scan refuses (a new kind
of command, a string literal, an attribute), the scan fails and names it;
the lists below are then edited by hand, in a commit that says why.
"""
import re
import sys
from pathlib import Path

LIBRARY_PREFIX = "VoltageToBit"
ALLOWED_IMPORT_ROOTS = ("Mathlib", LIBRARY_PREFIX)

ALLOWED_COMMAND_STARTS = (
    "import", "open", "namespace", "section", "end", "variable", "universe",
    "theorem", "lemma", "def", "structure", "inductive", "example",
    "noncomputable", "private", "protected",
)
# the words of ALLOWED_COMMAND_STARTS that may stand in front of another one
COMMAND_MODIFIERS = ("noncomputable", "private", "protected")

# word -> why it is refused
FORBIDDEN_WORDS = {}


def _forbid(reason, words):
    for word in words.split():
        FORBIDDEN_WORDS[word] = reason


_forbid("unfinished proof: the statement is accepted without a proof",
        "sorry admit sorryAx")
_forbid("the proof is delegated to compiled code that the kernel does not check",
        "native_decide ofReduceBool reduceBool ofReduceNat reduceNat trustCompiler")
_forbid("replaces or escapes the checked definition in compiled code",
        "implemented_by extern unsafe partial csimp")
_forbid("a declaration that is assumed, or whose body is hidden from the logic",
        "axiom opaque irreducible_def")
_forbid("an option can switch off the kernel check (debug.skipKernelTC) or change how "
        "statements are elaborated (autoImplicit)",
        "set_option skipKernelTC")
_forbid("runs arbitrary code while the file is compiled; such code can add declarations "
        "that the kernel never checked",
        "run_cmd run_elab run_meta run_tac by_elab initialize builtin_initialize "
        "addDeclWithoutChecking")
_forbid("defines new syntax or a new elaborator, after which the text no longer means "
        "what the standard grammar says",
        "elab elab_rules macro macro_rules syntax declare_syntax_cat notation notation3 "
        "infix infixl infixr prefix postfix binder_predicate unif_hint "
        "simproc simproc_decl dsimproc dsimproc_decl builtin_simproc builtin_dsimproc "
        "register_option register_builtin_option register_simp_attr register_label_attr")
_forbid("an instance or attribute changes which term the elaborator builds for later text",
        "instance attribute deriving class abbrev seal unseal")
_forbid("adds a hypothesis to later theorems without it appearing in their text",
        "include omit")
_forbid("makes a name refer to something other than what it appears to refer to",
        "renaming hiding export")

LAKEFILE_RULES = {
    None: {
        "name": r'"[A-Za-z0-9_.-]+"',
        "version": r'"[0-9A-Za-z_.+-]+"',
        "defaultTargets": r'\["[A-Za-z0-9_.]+"(, "[A-Za-z0-9_.]+")*\]',
    },
    "[leanOptions]": {
        # these are exact values, not shapes
        "pp.unicode.fun": r"true",
        "autoImplicit": r"false",
        "relaxedAutoImplicit": r"false",
    },
    "[[require]]": {
        "name": r'"[A-Za-z0-9_.-]+"',
        "git": r'"https://[A-Za-z0-9_./-]+"',
        "rev": r'"[A-Za-z0-9_.-]+"',
        "scope": r'"[A-Za-z0-9_.-]+"',
    },
    "[[lean_lib]]": {
        "name": r'"[A-Za-z0-9_.]+"',
    },
}


# ---------------------------------------------------------------------------
# Lean's identifier characters (Init/Meta/Defs.lean: isLetterLike,
# isSubScriptAlnum, isIdFirst, isIdRest)

def _is_letter_like(o):
    return ((0x3B1 <= o <= 0x3C9 and o != 0x3BB)
            or (0x391 <= o <= 0x3A9 and o not in (0x3A0, 0x3A3))
            or 0x3CA <= o <= 0x3FB
            or 0x1F00 <= o <= 0x1FFE
            or 0x2100 <= o <= 0x214F
            or 0x1D49C <= o <= 0x1D59F
            or (0x00C0 <= o <= 0x00FF and o not in (0x00D7, 0x00F7))
            or 0x0100 <= o <= 0x017F)


def _is_subscript_alnum(o):
    return (0x2080 <= o <= 0x2089 or 0x2090 <= o <= 0x209C
            or 0x1D62 <= o <= 0x1D6A or o == 0x2C7C)


def _is_ascii_alpha(ch):
    return "a" <= ch <= "z" or "A" <= ch <= "Z"


def is_id_first(ch):
    return _is_ascii_alpha(ch) or ch == "_" or _is_letter_like(ord(ch))


def is_id_rest(ch):
    o = ord(ch)
    return (_is_ascii_alpha(ch) or "0" <= ch <= "9" or ch in "_'!?"
            or _is_letter_like(o) or _is_subscript_alnum(o))


# ---------------------------------------------------------------------------
# Comment removal (Lean/Parser/Basic.lean: whitespace, finishCommentBlock)

def strip_comments(text):
    """Return (code, findings). `code` has the length of `text`; every
    character of a comment is replaced by a space, newlines are kept, so
    offsets, lines and columns are those of the file. `findings` is a list of
    (offset, rule, message)."""
    out = list(text)
    findings = []
    n = len(text)

    def blank(start, stop):
        for k in range(start, stop):
            if out[k] != "\n":
                out[k] = " "

    def comment_end(start):
        """Offset just after the comment that opens at `start`, or None."""
        j = start + 2
        if j < n and text[j] in "-!":       # "/--" and "/-!" are tokens of their own
            j += 1
        depth = 1
        while j < n:
            ch = text[j]
            j += 1
            if ch == "-":
                if j >= n:
                    return None
                if text[j] == "/":
                    j += 1
                    if depth == 1:
                        return j
                    depth -= 1
            elif ch == "/":
                if j >= n:
                    return None
                if text[j] == "-":
                    j += 1
                    depth += 1
        return None

    i = 0
    while i < n:
        ch = text[i]
        pair = text[i:i + 2]
        if pair in ("--", "/-"):
            before = text[i - 1] if i > 0 else "\n"
            if before not in " \n":
                findings.append((i, "lexical",
                                 f"comment opener `{pair}` directly after `{before}`: Lean may read "
                                 "this as code (the first character can belong to the token before "
                                 "it); put a space in front"))
                i += 2
                continue
            if pair == "--":
                j = text.find("\n", i)
                j = n if j < 0 else j
            else:
                j = comment_end(i)
                if j is None:
                    findings.append((i, "lexical", "unterminated comment"))
                    i += 2
                    continue
            blank(i, j)
            i = j
        elif ch == '"':
            findings.append((i, "lexical",
                             "double quote outside a comment: a string or character literal can hide "
                             "code from this scan (the library uses none)"))
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            i = min(j + 1, n)
        elif ch == "«":
            findings.append((i, "lexical",
                             "escaped identifier `«...»` outside a comment: it can hide code from "
                             "this scan (the library uses none)"))
            i += 1
        else:
            i += 1
    return "".join(out), findings


# ---------------------------------------------------------------------------
# Rules on the comment-free text

def words(code):
    """Maximal runs of identifier characters, as (offset, word)."""
    i, n = 0, len(code)
    while i < n:
        if is_id_rest(code[i]):
            j = i + 1
            while j < n and is_id_rest(code[j]):
                j += 1
            yield i, code[i:j]
            i = j
        else:
            i += 1


def split_run(run):
    """Where Lean starts a word inside a maximal run of identifier characters.

    Lean does not start an identifier with `'`, `!`, `?` or a subscript: in
    `!sorry` the `!` is a token of its own and `sorry` is the keyword. Returns
    (number of such leading characters, the rest of the run). The rest starts
    with a letter, `_` or a digit, or is empty."""
    k = 0
    while k < len(run) and not is_id_first(run[k]) and not "0" <= run[k] <= "9":
        k += 1
    return k, run[k:]


def scan_code(code):
    findings = []
    for offset, run in words(code):
        skipped, word = split_run(run)
        if word in FORBIDDEN_WORDS:
            findings.append((offset + skipped, "forbidden", f"`{word}`: {FORBIDDEN_WORDS[word]}"))
        elif word and "0" <= word[0] <= "9":
            # a numeral directly followed by a keyword is two tokens for Lean
            for bad, reason in FORBIDDEN_WORDS.items():
                if bad in word:
                    findings.append((offset + skipped, "forbidden",
                                     f"`{bad}` glued to a numeral in `{word}`: {reason}"))
                    break
    for match in re.finditer(r"@\[", code):
        findings.append((match.start(), "forbidden",
                         "`@[`: an attribute changes which term the elaborator builds for later "
                         "text, or how a definition is compiled"))
    for match in re.finditer(r"#", code):
        nxt = code[match.end():match.end() + 1]
        if nxt and is_id_first(nxt):
            findings.append((match.start(), "forbidden",
                             "`#` command: `#eval` runs arbitrary code while the file is compiled, "
                             "`#exit` makes Lean ignore the rest of the file"))
    for match in re.finditer(r"\+ *native(?![A-Za-z0-9_'!?])", code):
        findings.append((match.start(), "forbidden",
                         "`+native`: the proof is delegated to compiled code that the kernel does "
                         "not check"))
    return findings


def column0_commands(code):
    """(offset, first word or character, text) of every command that starts in
    column 0; the text of a command runs to the next line that starts in
    column 0."""
    starts = [m.start() for m in re.finditer(r"(?m)^[^ \n]", code)]
    for k, start in enumerate(starts):
        stop = starts[k + 1] if k + 1 < len(starts) else len(code)
        if is_id_rest(code[start]):
            j = start + 1
            while j < len(code) and is_id_rest(code[j]):
                j += 1
            head = code[start:j]
        else:
            head = code[start]
        yield start, head, code[start:stop]


def scan_commands(code, opens):
    findings = []
    for offset, head, text in column0_commands(code):
        if head not in ALLOWED_COMMAND_STARTS:
            findings.append((offset, "column-0",
                             f"a line starting in column 0 starts with `{head}`, which is not one of: "
                             + " ".join(ALLOWED_COMMAND_STARTS)))
            continue
        if head == "variable" and "[" in text:
            findings.append((offset + text.index("["), "variable",
                             "instance-implicit `variable`: Lean adds it to later theorems whose "
                             "text does not mention it"))
        if head == "import":
            first_line = text.split("\n", 1)[0]
            module = first_line[len("import"):].strip()
            if not re.fullmatch(r"[A-Za-z0-9_]+(\.[A-Za-z0-9_]+)*", module):
                findings.append((offset, "import", f"unexpected form of import: `{first_line.strip()}`"))
            elif module.split(".")[0] not in ALLOWED_IMPORT_ROOTS:
                findings.append((offset, "import",
                                 f"import of `{module}`: only modules of "
                                 + " and ".join(ALLOWED_IMPORT_ROOTS) + " are expected"))
        if head == "open":
            first_line = " ".join(text.split("\n", 1)[0].split())
            opens[first_line] = opens.get(first_line, 0) + 1
    # rule 3 (b): a word that starts a command must not occur anywhere else
    for offset, run in words(code):
        skipped, word = split_run(run)
        if word not in ALLOWED_COMMAND_STARTS:
            continue
        start = offset + skipped
        before = code[code.rfind("\n", 0, start) + 1:start]
        if before == "":
            continue
        if not before.startswith(" ") and all(w in COMMAND_MODIFIERS for w in before.split()):
            continue
        findings.append((start, "command",
                         f"`{word}` is not at the start of a line: the library is written with "
                         "every command starting in column 0, and only such commands are "
                         "looked at by the rules on commands, variables and imports"))
    return findings


def scan_lakefile(path):
    """Findings as (line number, message) for a lakefile.toml."""
    findings = []
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        return [(0, f"cannot read: {exc}")]
    section = None
    for number, line in enumerate(text.split("\n"), start=1):
        if not line.strip():
            continue
        if line in LAKEFILE_RULES:
            section = line
            continue
        match = re.fullmatch(r"([A-Za-z][A-Za-z0-9_.]*) = (.+)", line)
        allowed = LAKEFILE_RULES[section]
        if match and match.group(1) in allowed and re.fullmatch(allowed[match.group(1)], match.group(2)):
            continue
        where = "at top level" if section is None else f"in {section}"
        findings.append((number,
                         f"`{line}` {where} is not in the allow-list of scripts/lean_scan.py "
                         "(a compiler option or argument set here applies to every file)"))
    return findings


# ---------------------------------------------------------------------------

def position(text, offset):
    line = text.count("\n", 0, offset) + 1
    column = offset - (text.rfind("\n", 0, offset) + 1) + 1
    return line, column


def scan_file(path, opens):
    """Findings as (line, column, rule, message, source line)."""
    try:
        text = path.read_bytes().decode("utf-8")
    except UnicodeDecodeError as exc:
        return [(0, 0, "lexical", f"not UTF-8: {exc}", "")]
    code, findings = strip_comments(text)
    findings += scan_code(code)
    findings += scan_commands(code, opens)
    lines = text.split("\n")
    result = []
    for offset, rule, message in sorted(findings):
        line, column = position(text, offset)
        result.append((line, column, rule, message, lines[line - 1]))
    return result


def main(argv):
    lakefile = None
    paths = []
    args = list(argv)
    while args:
        arg = args.pop(0)
        if arg == "--lakefile":
            if not args:
                print(__doc__, file=sys.stderr)
                return 2
            lakefile = Path(args.pop(0))
        elif arg.startswith("-"):
            print(__doc__, file=sys.stderr)
            return 2
        else:
            paths.append(Path(arg))
    if not paths:
        print(__doc__, file=sys.stderr)
        return 2

    files = []
    for path in paths:
        if path.is_dir():
            files += sorted(p for p in path.rglob("*.lean") if p.is_file())
        elif path.is_file():
            files.append(path)
        else:
            print(f"lean_scan.py: no such file or directory: {path}", file=sys.stderr)
            return 2
    files = sorted(set(files), key=lambda p: p.as_posix())

    opens = {}
    count = 0
    lines = 0
    for path in files:
        lines += path.read_bytes().count(b"\n")
        for line, column, rule, message, source in scan_file(path, opens):
            count += 1
            print(f"{path.as_posix()}:{line}:{column}: [{rule}] {message}")
            if source.strip():
                print(f"    {source.strip()}")
    if lakefile is not None:
        if lakefile.with_name("lakefile.lean").exists():
            count += 1
            print(f"{lakefile.with_name('lakefile.lean').as_posix()}: [lakefile] a lakefile.lean is "
                  "arbitrary code; this scan only understands lakefile.toml")
        for number, message in scan_lakefile(lakefile):
            count += 1
            print(f"{lakefile.as_posix()}:{number}: [lakefile] {message}")

    scanned = f"{len(files)} Lean files ({lines} lines)"
    if lakefile is not None:
        scanned += f" and {lakefile.as_posix()}"
    print(f"scanned: {scanned}")
    for text in sorted(opens):
        print(f"allowed, for the record: `{text}` ({opens[text]} time(s))")
    if count:
        print(f"FORBIDDEN CONSTRUCTS FOUND: {count}")
        return 1
    print("no forbidden construct found")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
