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
      · rw [AExp.eval]
      · rfl
    · apply EIfFalse
      · rfl
      · apply EAsgn
        · rw [AExp.eval]
        · apply State.set_comm
          · simp
  -- apply ESeq
  -- · apply EAsgn
  --   · rfl
  --   · rfl
  -- · apply EIfFalse
  --   · rfl
  --   · apply EAsgn
  --     · rfl
  --     · simp only [AExp.eval]
  --       grind

theorem ceval_example2 :
  σ =[
    x = 0;
    y = 1;
    z = 2
  ]=> σ["z"↦2]["y"↦1]["x"↦0] := by
    apply ESeq
    · apply EAsgn
      · rw [AExp.eval]
      · rfl
    · apply ESeq
      · apply EAsgn
        · rw [AExp.eval]
        · rfl
      · apply EAsgn
        · rw [AExp.eval]
        · --rw [State.set_comm (by simp)]
          -- conv =>
          --   lhs;
          grind
          -- have zy : ("z" ≠ "y") := sorry
          -- have σ' := σ["z"↦2]["x"↦0]["y"↦1]
          -- have zx : ("z" ≠ "x") := sorry
          -- have yx : ("y" ≠ "x") := sorry
          -- exact State.set_comm yx (State.set_comm zx )
          -- sorry
