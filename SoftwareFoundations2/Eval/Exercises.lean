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
    · rfl -- eval 2 = eval 2
    · rfl -- σ[x -> eval 2] = σ[x -> eval 2]
  · simp only [AExp.eval]
    apply EIfFalse
    · rfl
    · apply EAsgn
      · unfold AExp.eval
        rfl -- 4 = 4
      · apply State.set_comm
        simp


theorem ceval_example2 :
  σ =[
    x = 0;
    y = 1;
    z = 2
  ]=> σ["z"↦2]["y"↦1]["x"↦0] := by
  apply ESeq
  · apply EAsgn
    · rfl
    · rfl
  · simp only [AExp.eval]
    apply ESeq
    · apply EAsgn
      · rfl
      · rfl
    · simp only [AExp.eval]
      apply EAsgn
      · rfl
      · simp [State.set_comm]

-- oltean@mailbox.org
