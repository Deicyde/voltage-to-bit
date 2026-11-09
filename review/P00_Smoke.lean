import VoltageToBit

/-! Smoke test: the frozen library is importable and the probe harness works. -/

open VoltageToBit VoltageToBit.Examples

#check @IsTrajectory.rise
#check @IsTrajectory.safe
#check @exists_solution
#print axioms illustrative_scenario
