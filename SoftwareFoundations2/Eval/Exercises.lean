import SoftwareFoundations2.Eval.Eval

open ComEval

theorem ceval_example1 :
  σ =[
      x = 2;
      if (x <= 1) then
        y = 3;
      else
        z = 4;
      endif
  ]=> σ["z" ↦ 4]["x" ↦ 2] := by
  apply ESeq
  · apply EAsgn
    · rfl
    · rfl
  · apply EIfFalse
    · rfl
    · apply EAsgn
      · rfl
      · simp only [AExp.eval]
        grind
