import Mathlib.Analysis.Calculus.MeanValue

/-!
# Scalar reachability lemmas

Generic facts about a real signal `v` on `[a, b]` that is continuous and has a
right derivative `v' t` at every `t ∈ [a, b)`. Nothing here mentions circuits.

* `barrier_le`, `barrier_ge`: a level that the signal can only leave "inwards"
  is never crossed.
* `rise_by`, `fall_by`: if the slope is at least `m > 0` towards a level `c`
  whenever the signal is on the wrong side of `c`, then the signal is on the
  right side of `c` from an explicit deadline on, and stays there.
* `rise_chain`, `fall_chain`: the same with a list of intermediate levels, each
  with its own slope bound. The deadline is a sum over segments.
-/

namespace VoltageToBit

open Set

/-- If `v a ≤ c` and the right derivative is negative at every time where
`v = c`, then `v ≤ c` on `[a, b]`. -/
theorem barrier_le {v v' : ℝ → ℝ} {a b c : ℝ}
    (hv : ContinuousOn v (Icc a b))
    (hv' : ∀ t ∈ Ico a b, HasDerivWithinAt v (v' t) (Ici t) t)
    (ha : v a ≤ c)
    (hbound : ∀ t ∈ Ico a b, v t = c → v' t < 0) :
    ∀ t ∈ Icc a b, v t ≤ c := by
  intro t ht
  exact image_le_of_deriv_right_lt_deriv_boundary' (B := fun _ => c) (B' := fun _ => 0)
    hv hv' ha continuousOn_const (fun x _ => hasDerivWithinAt_const x _ c) hbound ht

/-- If `c ≤ v a` and the right derivative is positive at every time where
`v = c`, then `c ≤ v` on `[a, b]`. -/
theorem barrier_ge {v v' : ℝ → ℝ} {a b c : ℝ}
    (hv : ContinuousOn v (Icc a b))
    (hv' : ∀ t ∈ Ico a b, HasDerivWithinAt v (v' t) (Ici t) t)
    (ha : c ≤ v a)
    (hbound : ∀ t ∈ Ico a b, v t = c → 0 < v' t) :
    ∀ t ∈ Icc a b, c ≤ v t := by
  intro t ht
  exact image_le_of_deriv_right_lt_deriv_boundary' (f := fun _ => c) (f' := fun _ => 0)
    continuousOn_const (fun x _ => hasDerivWithinAt_const x _ c) ha hv hv'
    (fun x hx h => hbound x hx h.symm) ht

/-- **Rise by a deadline, and stay.** If the right derivative is at least
`m > 0` whenever `v ≤ c`, and `l ≤ v a`, then `c ≤ v t` for every
`t ∈ [a, b]` with `a + (c - l) / m ≤ t`. -/
theorem rise_by {v v' : ℝ → ℝ} {a b c l m : ℝ}
    (hv : ContinuousOn v (Icc a b))
    (hv' : ∀ t ∈ Ico a b, HasDerivWithinAt v (v' t) (Ici t) t)
    (hm : 0 < m) (hl : l ≤ v a)
    (hslope : ∀ t ∈ Ico a b, v t ≤ c → m ≤ v' t) :
    ∀ t ∈ Icc a b, a + (c - l) / m ≤ t → c ≤ v t := by
  intro t ht htime
  by_contra hlt
  push Not at hlt
  by_cases hex : ∃ s ∈ Icc a t, c ≤ v s
  · -- once at or above `c`, the barrier keeps the signal there
    obtain ⟨s, hs, hcs⟩ := hex
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    have hsubo : Ico s t ⊆ Ico a b := Ico_subset_Ico hs.1 ht.2
    have h := barrier_ge (hv.mono hsub) (fun x hx => hv' x (hsubo hx)) hcs
      (fun x hx hx' => lt_of_lt_of_le hm (hslope x (hsubo hx) hx'.le)) t ⟨hs.2, le_rfl⟩
    linarith
  · -- otherwise the signal is below `c` on all of `[a, t]` and climbs at rate `m`
    push Not at hex
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    have hsubo : Ico a t ⊆ Ico a b := Ico_subset_Ico le_rfl ht.2
    have key : l + m * (t - a) ≤ v t :=
      image_le_of_deriv_right_le_deriv_boundary
        (f := fun s => l + m * (s - a)) (f' := fun _ => m) (a := a) (b := t)
        (by fun_prop)
        (fun x _ => by
          have h := (((hasDerivAt_id x).sub_const a).const_mul m).const_add l
          simpa using h.hasDerivWithinAt)
        (B := v) (B' := v') (by simpa using hl) (hv.mono hsub)
        (fun x hx => hv' x (hsubo hx))
        (fun x hx => hslope x (hsubo hx) (hex x ⟨hx.1, hx.2.le⟩).le) ⟨ht.1, le_rfl⟩
    have h1 : (c - l) / m ≤ t - a := by linarith
    have h2 : c - l ≤ (t - a) * m := (div_le_iff₀ hm).mp h1
    nlinarith

/-- **Fall by a deadline, and stay.** Mirror image of `rise_by`. -/
theorem fall_by {v v' : ℝ → ℝ} {a b c h m : ℝ}
    (hv : ContinuousOn v (Icc a b))
    (hv' : ∀ t ∈ Ico a b, HasDerivWithinAt v (v' t) (Ici t) t)
    (hm : 0 < m) (hh : v a ≤ h)
    (hslope : ∀ t ∈ Ico a b, c ≤ v t → v' t ≤ -m) :
    ∀ t ∈ Icc a b, a + (h - c) / m ≤ t → v t ≤ c := by
  intro t ht htime
  have key := rise_by (v := fun s => -v s) (v' := fun s => -v' s) (a := a) (b := b)
    (c := -c) (l := -h) (m := m) hv.neg (fun x hx => (hv' x hx).neg) hm (by simpa using hh)
    (fun x hx hx' => by
      have := hslope x hx (by simpa using hx')
      linarith) t ht (by
      have : (-c - -h) / m = (h - c) / m := by ring
      rw [this]; exact htime)
  simpa using key

/-! ## Multi-segment bounds -/

/-- Total deadline for a list of segments `(c, m)` (level, slope bound),
starting from level `l`: the sum of `(c - previous level) / m`. -/
noncomputable def riseTime (l : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => 0
  | (c, m) :: rest => (c - l) / m + riseTime c rest

/-- The last level of a list of segments (or `l` for the empty list). -/
def finalLevel (l : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => l
  | (c, _) :: rest => finalLevel c rest

/-- Levels are nondecreasing starting from `l`, and all slope bounds are positive. -/
def RiseSegs (l : ℝ) : List (ℝ × ℝ) → Prop
  | [] => True
  | (c, m) :: rest => l ≤ c ∧ 0 < m ∧ RiseSegs c rest

theorem RiseSegs.pos : ∀ {segs : List (ℝ × ℝ)} {l : ℝ}, RiseSegs l segs → ∀ p ∈ segs, 0 < p.2
  | [], _, _, p, hp => by simp at hp
  | (c, m) :: rest, _, h, p, hp => by
    obtain ⟨-, hm, hrest⟩ := h
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact hm
    · exact RiseSegs.pos hrest p hp'

theorem RiseSegs.le_finalLevel :
    ∀ {segs : List (ℝ × ℝ)} {l : ℝ}, RiseSegs l segs → l ≤ finalLevel l segs
  | [], _, _ => le_rfl
  | (_, _) :: _, _, h => le_trans h.1 (RiseSegs.le_finalLevel h.2.2)

/-- In a valid rising list every level is at or below the final level. -/
theorem RiseSegs.mem_le_finalLevel :
    ∀ {segs : List (ℝ × ℝ)} {l : ℝ}, RiseSegs l segs → ∀ p ∈ segs, p.1 ≤ finalLevel l segs
  | [], _, _, p, hp => by simp at hp
  | (c, m) :: rest, _, h, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact RiseSegs.le_finalLevel h.2.2
    · exact RiseSegs.mem_le_finalLevel h.2.2 p hp'

theorem riseTime_nonneg : ∀ (segs : List (ℝ × ℝ)) (l : ℝ), RiseSegs l segs → 0 ≤ riseTime l segs
  | [], _, _ => le_rfl
  | (c, m) :: rest, l, h => by
    obtain ⟨hlc, hm, hrest⟩ := h
    have h1 : 0 ≤ (c - l) / m := div_nonneg (by linarith) hm.le
    have h2 := riseTime_nonneg rest c hrest
    simp only [riseTime]
    linarith

/-- **Multi-segment rise.** For a nonempty list of segments `(c, m)`, if the
right derivative is at least `m` whenever `v ≤ c` (for each segment), then from
any time `s` with `l ≤ v s`, the signal is at or above the final level from
`s + riseTime l segs` on. -/
theorem rise_chain {v v' : ℝ → ℝ} {a b : ℝ}
    (hv : ContinuousOn v (Icc a b))
    (hv' : ∀ t ∈ Ico a b, HasDerivWithinAt v (v' t) (Ici t) t) :
    ∀ (rest : List (ℝ × ℝ)) (c m l s : ℝ), RiseSegs l ((c, m) :: rest) →
      (∀ p ∈ (c, m) :: rest, ∀ t ∈ Ico a b, v t ≤ p.1 → p.2 ≤ v' t) →
      s ∈ Icc a b → l ≤ v s →
      ∀ t ∈ Icc s b, s + riseTime l ((c, m) :: rest) ≤ t →
        finalLevel l ((c, m) :: rest) ≤ v t := by
  intro rest
  induction rest with
  | nil =>
    intro c m l s hsegs hslope hs hl t ht htime
    obtain ⟨_, hm, _⟩ := hsegs
    have hsub : Icc s b ⊆ Icc a b := Icc_subset_Icc hs.1 le_rfl
    have hsubo : Ico s b ⊆ Ico a b := Ico_subset_Ico hs.1 le_rfl
    simp only [riseTime, add_zero] at htime
    exact rise_by (hv.mono hsub) (fun x hx => hv' x (hsubo hx)) hm hl
      (fun x hx => hslope (c, m) (by simp) x (hsubo hx)) t ht htime
  | cons p rest ih =>
    intro c m l s hsegs hslope hs hl t ht htime
    obtain ⟨c₂, m₂⟩ := p
    obtain ⟨hlc, hm, hrest⟩ := hsegs
    have hsub : Icc s b ⊆ Icc a b := Icc_subset_Icc hs.1 le_rfl
    have hsubo : Ico s b ⊆ Ico a b := Ico_subset_Ico hs.1 le_rfl
    have hnn : 0 ≤ riseTime c ((c₂, m₂) :: rest) := riseTime_nonneg _ _ hrest
    have hd : 0 ≤ (c - l) / m := div_nonneg (by linarith) hm.le
    simp only [riseTime] at htime hnn
    -- first segment: at time `s₁` the signal is at or above `c`
    set s₁ := s + (c - l) / m with hs₁
    have hs₁t : s₁ ≤ t := by linarith
    have hs₁mem : s₁ ∈ Icc s b := ⟨by linarith, le_trans hs₁t ht.2⟩
    have hc : c ≤ v s₁ := rise_by (hv.mono hsub) (fun x hx => hv' x (hsubo hx)) hm hl
      (fun x hx => hslope (c, m) (by simp) x (hsubo hx)) s₁ hs₁mem le_rfl
    -- remaining segments, started at `s₁` from level `c`
    have := ih c₂ m₂ c s₁ hrest (fun p hp => hslope p (List.mem_cons_of_mem _ hp))
      ⟨le_trans hs.1 hs₁mem.1, hs₁mem.2⟩ hc t ⟨hs₁t, ht.2⟩ (by simp only [riseTime]; linarith)
    simpa [finalLevel] using this

/-- Total deadline for a falling list of segments, starting from level `h`. -/
noncomputable def fallTime (h : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => 0
  | (c, m) :: rest => (h - c) / m + fallTime c rest

/-- Levels are nonincreasing starting from `h`, and all slope bounds are positive. -/
def FallSegs (h : ℝ) : List (ℝ × ℝ) → Prop
  | [] => True
  | (c, m) :: rest => c ≤ h ∧ 0 < m ∧ FallSegs c rest

theorem FallSegs.pos : ∀ {segs : List (ℝ × ℝ)} {h : ℝ}, FallSegs h segs → ∀ p ∈ segs, 0 < p.2
  | [], _, _, p, hp => by simp at hp
  | (c, m) :: rest, _, hs, p, hp => by
    obtain ⟨-, hm, hrest⟩ := hs
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact hm
    · exact FallSegs.pos hrest p hp'

theorem FallSegs.finalLevel_le :
    ∀ {segs : List (ℝ × ℝ)} {h : ℝ}, FallSegs h segs → finalLevel h segs ≤ h
  | [], _, _ => le_rfl
  | (c, _) :: rest, h, hs => by
    show finalLevel c rest ≤ h
    exact le_trans (FallSegs.finalLevel_le hs.2.2) hs.1

/-- In a valid falling list every level is at or above the final level. -/
theorem FallSegs.finalLevel_le_mem :
    ∀ {segs : List (ℝ × ℝ)} {h : ℝ}, FallSegs h segs → ∀ p ∈ segs, finalLevel h segs ≤ p.1
  | [], _, _, p, hp => by simp at hp
  | (c, m) :: rest, _, hs, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact FallSegs.finalLevel_le hs.2.2
    · exact FallSegs.finalLevel_le_mem hs.2.2 p hp'

theorem fallTime_nonneg : ∀ (segs : List (ℝ × ℝ)) (h : ℝ), FallSegs h segs → 0 ≤ fallTime h segs
  | [], _, _ => le_rfl
  | (c, m) :: rest, h, hs => by
    obtain ⟨hch, hm, hrest⟩ := hs
    have h1 : 0 ≤ (h - c) / m := div_nonneg (by linarith) hm.le
    have h2 := fallTime_nonneg rest c hrest
    simp only [fallTime]
    linarith

/-- **Multi-segment fall.** Mirror image of `rise_chain`. -/
theorem fall_chain {v v' : ℝ → ℝ} {a b : ℝ}
    (hv : ContinuousOn v (Icc a b))
    (hv' : ∀ t ∈ Ico a b, HasDerivWithinAt v (v' t) (Ici t) t) :
    ∀ (rest : List (ℝ × ℝ)) (c m h s : ℝ), FallSegs h ((c, m) :: rest) →
      (∀ p ∈ (c, m) :: rest, ∀ t ∈ Ico a b, p.1 ≤ v t → v' t ≤ -p.2) →
      s ∈ Icc a b → v s ≤ h →
      ∀ t ∈ Icc s b, s + fallTime h ((c, m) :: rest) ≤ t →
        v t ≤ finalLevel h ((c, m) :: rest) := by
  intro rest
  induction rest with
  | nil =>
    intro c m h s hsegs hslope hs hh t ht htime
    obtain ⟨_, hm, _⟩ := hsegs
    have hsub : Icc s b ⊆ Icc a b := Icc_subset_Icc hs.1 le_rfl
    have hsubo : Ico s b ⊆ Ico a b := Ico_subset_Ico hs.1 le_rfl
    simp only [fallTime, add_zero] at htime
    exact fall_by (hv.mono hsub) (fun x hx => hv' x (hsubo hx)) hm hh
      (fun x hx => hslope (c, m) (by simp) x (hsubo hx)) t ht htime
  | cons p rest ih =>
    intro c m h s hsegs hslope hs hh t ht htime
    obtain ⟨c₂, m₂⟩ := p
    obtain ⟨hch, hm, hrest⟩ := hsegs
    have hsub : Icc s b ⊆ Icc a b := Icc_subset_Icc hs.1 le_rfl
    have hsubo : Ico s b ⊆ Ico a b := Ico_subset_Ico hs.1 le_rfl
    have hnn : 0 ≤ fallTime c ((c₂, m₂) :: rest) := fallTime_nonneg _ _ hrest
    have hd : 0 ≤ (h - c) / m := div_nonneg (by linarith) hm.le
    simp only [fallTime] at htime hnn
    set s₁ := s + (h - c) / m with hs₁
    have hs₁t : s₁ ≤ t := by linarith
    have hs₁mem : s₁ ∈ Icc s b := ⟨by linarith, le_trans hs₁t ht.2⟩
    have hc : v s₁ ≤ c := fall_by (hv.mono hsub) (fun x hx => hv' x (hsubo hx)) hm hh
      (fun x hx => hslope (c, m) (by simp) x (hsubo hx)) s₁ hs₁mem le_rfl
    have := ih c₂ m₂ c s₁ hrest (fun p hp => hslope p (List.mem_cons_of_mem _ hp))
      ⟨le_trans hs.1 hs₁mem.1, hs₁mem.2⟩ hc t ⟨hs₁t, ht.2⟩ (by simp only [fallTime]; linarith)
    simpa [finalLevel] using this

end VoltageToBit
