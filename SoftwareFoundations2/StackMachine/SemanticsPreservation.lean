import SoftwareFoundations2.StackMachine.Compile
import SoftwareFoundations2.StackMachine.Lemmas
import SoftwareFoundations2.Eval.Eval

set_option linter.style.longLine false
attribute [local simp] Except.instMonad
attribute [local simp] Except.bind

open Instruction AExp BExp

@[simp]
def Bool.toValue : Bool → Value
  | false => 0
  | true  => 1

/- The bulk of work for semantics preservation will be handled by the following
   auxiliary lemmas: -/

lemma AExp.compileCorrectAux {pre suf stack mem} (a : AExp) :
  Reachable
    (.ok ⟨pre ++ (a.compile ++ suf), stack, mem, pre.length⟩)
    (.ok ⟨pre ++ (a.compile ++ suf), a.eval mem :: stack, mem, (pre ++ a.compile).length⟩) := by
  induction a generalizing pre suf stack with
  | ANum n =>
      simp only [compile]
      apply Reachable.step
      simp [step, fetchInstr, replaceStackAndIncrPC, incrPC]
  | AId x =>
      simp only [compile]
      apply Reachable.step
      simp [step, fetchInstr, replaceStackAndIncrPC, incrPC]
  | APlus a1 a2 ih1 ih2 =>
      simp only [List.length_append] at ih2
      simp only [compile, List.append_assoc, eval, List.length_append]
      apply Reachable.trans ih1
      rw [List.length_append, ←List.append_assoc]
      apply @Reachable.trans _ _ (.ok {
          code := pre ++ a1.compile ++ (a2.compile ++ ADD :: suf),
          stack := eval mem a2 :: eval mem a1 :: stack,
          mem := mem,
          pc := pre.length + a1.compile.length + a2.compile.length
        })
      · rw [←List.length_append]
        apply ih2
      · apply Reachable.step
        rw [step, fetchInstr]
        simp [←Nat.add_assoc]
        have : pre.length + a1.compile.length + a2.compile.length <
          pre.length + a1.compile.length + a2.compile.length + suf.length + 1 := by omega
        simp [this, ←List.append_assoc, stackPeek2, replaceStackAndIncrPC, incrPC]
  | AMinus a1 a2 ih1 ih2 =>
      simp only [List.length_append] at ih2
      simp only [compile, List.append_assoc, eval, List.length_append]
      apply Reachable.trans ih1
      rw [List.length_append, ←List.append_assoc]
      apply @Reachable.trans _ _ (.ok {
          code := pre ++ a1.compile ++ (a2.compile ++ SUB :: suf),
          stack := eval mem a2 :: eval mem a1 :: stack,
          mem := mem,
          pc := pre.length + a1.compile.length + a2.compile.length
        })
      · rw [←List.length_append]
        apply ih2
      · apply Reachable.step
        rw [step, fetchInstr]
        simp [←Nat.add_assoc]
        have : pre.length + a1.compile.length + a2.compile.length <
          pre.length + a1.compile.length + a2.compile.length + suf.length + 1 := by omega
        simp [this, ←List.append_assoc, stackPeek2, replaceStackAndIncrPC, incrPC]
  | AMult a1 a2 ih1 ih2 =>
      simp only [List.length_append] at ih2
      simp only [compile, List.append_assoc, eval, List.length_append]
      apply Reachable.trans ih1
      rw [List.length_append, ←List.append_assoc]
      apply @Reachable.trans _ _ (.ok {
          code := pre ++ a1.compile ++ (a2.compile ++ MUL :: suf),
          stack := eval mem a2 :: eval mem a1 :: stack,
          mem := mem,
          pc := pre.length + a1.compile.length + a2.compile.length
        })
      · rw [←List.length_append]
        apply ih2
      · apply Reachable.step
        rw [step, fetchInstr]
        simp [←Nat.add_assoc]
        have : pre.length + a1.compile.length + a2.compile.length <
          pre.length + a1.compile.length + a2.compile.length + suf.length + 1 := by omega
        simp [this, ←List.append_assoc, stackPeek2, replaceStackAndIncrPC, incrPC]

lemma BExp.compileCorrectAux {pre suf stack mem} (b : BExp) :
  Reachable
    (.ok ⟨pre ++ (b.compile ++ suf), stack, mem, pre.length⟩)
    (.ok ⟨pre ++ (b.compile ++ suf), (b.eval mem).toValue :: stack, mem, (pre ++ b.compile).length⟩) := by
    induction b generalizing pre suf stack with
    | BTrue =>
      apply Reachable.step
      simp only [compile]
      simp [step, fetchInstr, replaceStackAndIncrPC, incrPC]
    | BFalse =>
      apply Reachable.step
      simp only [compile]
      simp [step, fetchInstr, replaceStackAndIncrPC, incrPC]
    | BEq a1 a2 =>
      simp only [compile, List.append_assoc, eval, List.length_append]
      apply Reachable.trans
      · apply AExp.compileCorrectAux
      · apply Reachable.trans
        · rw [←List.append_assoc]
          apply AExp.compileCorrectAux a2
        · apply Reachable.step
          simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, stackPeek2]
          by_cases h : AExp.eval mem a1 = AExp.eval mem a2
          · simp +arith [h]
          · simp +arith [h]
            have : (AExp.eval mem a1 == AExp.eval mem a2) = false := by
              simp only [beq_eq_false_iff_ne]
              assumption
            simp only [this]
    | BNeq a1 a2 =>
      simp only [compile, List.append_assoc, eval, List.length_append]
      apply Reachable.trans
      · apply AExp.compileCorrectAux
      · apply Reachable.trans
        · rw [←List.append_assoc]
          apply AExp.compileCorrectAux a2
        · apply Reachable.trans (Reachable.step rfl)
          simp only [step, Except.instMonad, Except.bind, fetchInstr, List.append_assoc, List.length_append,
            Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left, Nat.le_refl,
            Nat.sub_self, replaceStackAndIncrPC, incrPC, stackPeek2, beq_iff_eq]
          by_cases h : AExp.eval mem a1 = AExp.eval mem a2
          · simp +arith only [h, bne_self_eq_false]
            apply Reachable.step
            simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, stackPeek1, ←List.append_assoc]
          · simp +arith only [h]
            have : (AExp.eval mem a1 != AExp.eval mem a2) = true := by
              simp only [bne_iff_ne, ne_eq]
              assumption
            simp only [this]
            apply Reachable.step
            simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, stackPeek1, ←List.append_assoc]
    | BLe a1 a2 =>
      simp only [compile, List.append_assoc, eval, List.length_append]
      apply Reachable.trans
      · apply AExp.compileCorrectAux
      · apply Reachable.trans
        · rw [←List.append_assoc]
          apply AExp.compileCorrectAux a2
        · apply Reachable.step
          simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, stackPeek2]
          by_cases h : AExp.eval mem a1 ≤ AExp.eval mem a2 <;> simp +arith [h]
    | BGt a1 a2 =>
      simp only [compile, List.append_assoc, eval, List.length_append]
      apply Reachable.trans
      · apply AExp.compileCorrectAux
      · apply Reachable.trans
        · rw [←List.append_assoc]
          apply AExp.compileCorrectAux a2
        · apply Reachable.trans
          · apply Reachable.step
            rfl
          · simp only [step, Except.instMonad, Except.bind, fetchInstr, List.append_assoc, List.length_append,
              Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left, Nat.le_refl,
              Nat.sub_self, replaceStackAndIncrPC, incrPC, stackPeek2, beq_iff_eq]
            by_cases h : AExp.eval mem a1 ≤ AExp.eval mem a2
            · simp +arith only [h]
              apply Reachable.step
              simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, stackPeek1, ←List.append_assoc]
              have h : (AExp.eval mem a2 < AExp.eval mem a1) = false := by
                simp only [Bool.false_eq_true, eq_iff_iff, iff_false, Nat.not_lt, h]
              simp only [h, Bool.false_eq_true, decide_false]
            · simp +arith only [h]
              apply Reachable.step
              simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, stackPeek1, ←List.append_assoc]
              have : (AExp.eval mem a2 < AExp.eval mem a1) = true := by
                simp only [Nat.not_le] at h
                simp only [h]
              simp only [this, decide_true]
    | BNot b1 ih =>
        simp only [compile, List.append_assoc, eval, List.length_append]
        apply Reachable.trans
        · apply ih
        · apply Reachable.step
          simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, stackPeek2, stackPeek1]
          by_cases h : eval mem b1 = true <;> simp [h] <;> omega
    | BAnd b1 b2 ih1 ih2 =>
        simp only [compile, List.append_assoc, eval, List.length_append]
        apply Reachable.trans ih1
        rw [←List.append_assoc]
        apply Reachable.trans ih2
        apply Reachable.step
        simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, stackPeek2]
        by_cases h1 : eval mem b1 = true <;> by_cases h2 : eval mem b2 = true
        all_goals
        simp only [h1, h2, Nat.mul_one, Bool.and_true, true_and, Bool.and_false]
        omega

/- For this proof, don't be set off if it becomes super technical and long.
   You can likely split the definition of Com.compileOffset into multiple sub-operations,
   and prove sub-lemmas for each sub-operation.
   But you don't have to; the naive way of proving this will likely suffice.
-/
lemma Com.compileCorrectAux (pgm σ σ' stack pre suf) (h : σ =[pgm]=> σ') :
  Reachable
    (.ok ⟨pre ++ pgm.compileOffset pre.length ++ suf, stack, σ, pre.length⟩)
    (.ok ⟨pre ++ pgm.compileOffset pre.length ++ suf, stack, σ', (pre ++ pgm.compileOffset pre.length).length⟩) := by
    induction pgm generalizing stack pre suf σ σ' with
    | CSkip =>
      apply Reachable.step
      simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, compileOffset]
      cases h ; rfl
    | CAsgn x a =>
      simp only [compileOffset]
      rw [List.append_assoc, List.append_assoc]
      apply Reachable.trans (AExp.compileCorrectAux a)
      apply Reachable.step
      simp only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append, List.cons_append, List.nil_append,
    List.length_cons, Nat.add_lt_add_iff_left, Nat.lt_add_right_iff_pos, Nat.zero_lt_succ, ↓reduceDIte,
    Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left, Nat.le_refl, Nat.sub_self,
    List.getElem_cons_zero, replaceStackAndIncrPC, incrPC, stackPeek1, replaceMemStackAndIncrPC, beq_iff_eq, gt_iff_lt,
    List.length_nil, Nat.zero_add, Except.ok.injEq, MachineState.mk.injEq, true_and]
      cases h with
      | EAsgn hv hs =>
        rw [hv] at hs
        exact And.intro (symm hs) (by omega)
    | CSeq c1 c2 ih1 ih2 =>
      simp only [compileOffset, List.append_assoc, List.length_append]
      simp only [List.append_assoc] at *
      cases h with
      | ESeq c1 c2 =>
        apply Reachable.trans (ih1 _ _ _ _ _ c1)
        rw [←List.append_assoc, ←Nat.add_assoc, ←List.length_append, ←List.length_append]
        exact ih2 _ _ _ _ _ c2
    | CIf b c1 c2 ih1 ih2 =>
      simp only [compileOffset, List.append_assoc, List.cons_append, List.nil_append,
        List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
      apply Reachable.trans (BExp.compileCorrectAux b)
      rw [←List.append_assoc pre b.compile]
      by_cases hx : BExp.eval σ b = true
      · apply Reachable.trans (Reachable.step rfl)
        simp only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append,
          List.append_assoc, List.length_cons, Nat.add_lt_add_iff_left, Nat.lt_add_right_iff_pos,
          Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, ↓reduceDIte, Nat.le_add_right,
          List.getElem_append_right, Nat.add_sub_cancel_left, Nat.le_refl, Nat.sub_self,
          List.getElem_cons_zero, Bool.toValue, hx, replaceStackAndIncrPC, incrPC, stackPeek2,
          beq_iff_eq, gt_iff_lt]
        apply Reachable.trans (Reachable.step rfl)
        simp +arith only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append,
          List.length_cons, ↓reduceDIte, List.getElem_append_right, replaceStackAndIncrPC, incrPC,
          stackPeek2, Nat.le_add_left, Nat.sub_eq_zero_of_le, Nat.one_mul, beq_iff_eq,
          Nat.right_eq_add, Nat.add_eq_zero_iff, List.length_eq_zero_iff, reduceCtorEq, and_false,
          ↓reduceIte, gt_iff_lt, Nat.lt_add_one]
        simp +arith only [List.getElem_append, ← List.append_assoc]
        have h' : ¬ (pre.length + b.compile.length + 1 - pre.length < b.compile.length) := by omega
        have h2 : pre.length + b.compile.length + 1 - pre.length - b.compile.length = 1 := by omega
        simp only [h', ↓reduceDIte, h2, List.getElem_cons_succ, List.getElem_cons_zero,
          List.append_assoc]
        cases h with
        | EIfTrue hv c' =>
          simp only[← List.append_assoc]
          convert Reachable.trans (ih1 _ _ _ _ _ c') _ using 1
          · rw [← List.singleton_append]
            nth_rewrite 2 [←List.singleton_append]
            nth_rewrite 3 [←List.singleton_append]
            nth_rewrite 4 [←List.singleton_append]
            have : 4 = ([PUSH ((pre ++ b.compile).length + 4)] ++ [JUMPI] ++
                [PUSH ((pre ++ b.compile ++ compileOffset ((pre ++ b.compile).length + 4) c1).length + 6)] ++
              [JUMP]).length := by
              simp
            nth_rewrite 9 [this]
            nth_rewrite 3 [this]
            simp only [← List.append_assoc]
            simp only [← List.length_append]
            have : pre ++ b.compile ++ [PUSH ((pre ++ b.compile).length + 4)] ++ [JUMPI] ++
                [PUSH ((pre ++ b.compile ++ compileOffset ((pre ++ b.compile).length + 4) c1).length + 6)] ++
              [JUMP] = pre ++ b.compile ++
                  ([PUSH ((pre ++ b.compile).length + 4)] ++ [JUMPI] ++
                      [PUSH ((pre ++ b.compile ++ compileOffset ((pre ++ b.compile).length + 4) c1).length + 6)] ++
                    [JUMP]) := by simp
            rw [this]
          · apply Reachable.trans (Reachable.step rfl)
            simp only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append,
              List.cons_append, List.nil_append, List.append_assoc, List.length_cons,
              List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.add_lt_add_iff_left,
              Nat.add_lt_add_iff_right, Nat.lt_add_right_iff_pos, Nat.lt_add_left_iff_pos,
              Nat.zero_lt_succ, ↓reduceDIte, Nat.le_add_right, List.getElem_append_right,
              Nat.add_sub_cancel_left, List.getElem_cons_succ, Nat.le_refl, Nat.sub_self,
              List.getElem_cons_zero, replaceStackAndIncrPC, incrPC, stackPeek2, beq_iff_eq,
              gt_iff_lt]
            apply Reachable.step
            simp +arith [step, fetchInstr, replaceStackAndIncrPC, incrPC, stackPeek2, stackPeek1, replaceMemStackAndIncrPC]
            have : pre.length + b.compile.length +
              (compileOffset (pre.length + b.compile.length + 4) c1).length + 5 -
              pre.length = b.compile.length + (compileOffset (pre.length + b.compile.length + 4) c1).length + 5 := by omega
            simp +arith [this]
            simp +arith [List.getElem_cons, List.getElem_append]
            have : b.compile.length + (compileOffset (pre.length + b.compile.length + 4) c1).length + 5 - b.compile.length =
              (compileOffset (pre.length + b.compile.length + 4) c1).length + 5 := by omega
            simp +arith [this]
        | EIfFalse hv => simp only [hx, Bool.true_eq_false] at hv
      · apply Reachable.trans (Reachable.step rfl)
        simp only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append,
          List.append_assoc, List.length_cons, Nat.add_lt_add_iff_left, Nat.lt_add_right_iff_pos,
          Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, ↓reduceDIte, Nat.le_add_right,
          List.getElem_append_right, Nat.add_sub_cancel_left, Nat.le_refl, Nat.sub_self,
          List.getElem_cons_zero, Bool.toValue, hx, replaceStackAndIncrPC, incrPC, stackPeek2,
          beq_iff_eq, gt_iff_lt]
        apply Reachable.trans (Reachable.step rfl)
        simp +arith only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append,
          List.length_cons, ↓reduceDIte, List.getElem_append_right, replaceStackAndIncrPC, incrPC,
          stackPeek2, Nat.zero_add, Nat.le_add_left, Nat.sub_eq_zero_of_le, Nat.zero_mul,
          beq_iff_eq, Nat.right_eq_add, Nat.add_eq_zero_iff, List.length_eq_zero_iff, reduceCtorEq,
          and_false, ↓reduceIte, gt_iff_lt, Nat.lt_irrefl]
        have : pre.length + b.compile.length + 1 - pre.length = b.compile.length + 1 := by omega
        simp +arith only [this, Nat.le_add_right, List.getElem_append_right,
          Nat.add_sub_cancel_left, List.getElem_cons_succ, List.getElem_cons_zero]
        apply Reachable.trans (Reachable.step rfl)
        simp +arith only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append,
          List.length_cons, ↓reduceDIte, List.getElem_append_right, replaceStackAndIncrPC, incrPC,
          stackPeek2, beq_iff_eq, gt_iff_lt]
        have : pre.length + b.compile.length + 2 - pre.length = b.compile.length + 2 := by omega
        simp +arith only [this, Nat.le_add_right, List.getElem_append_right,
          Nat.add_sub_cancel_left, List.getElem_cons_succ, List.getElem_cons_zero]
        apply Reachable.trans (Reachable.step rfl)
        simp +arith only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append,
          List.length_cons, ↓reduceDIte, List.getElem_append_right, replaceStackAndIncrPC, incrPC,
          stackPeek2, beq_iff_eq, gt_iff_lt]
        have : pre.length + b.compile.length + 3 - pre.length = b.compile.length + 3 := by omega
        simp +arith only [this, Nat.le_add_right, List.getElem_append_right,
          Nat.add_sub_cancel_left, List.getElem_cons_succ, List.getElem_cons_zero, stackPeek1]
        cases h with
        | EIfTrue hv => contradiction
        | EIfFalse hv c' =>
          convert Reachable.trans (ih2 σ σ' stack _ _ c') _ using 1
          · rw [← List.singleton_append]
            nth_rewrite 2 [←List.singleton_append]
            nth_rewrite 3 [←List.singleton_append]
            nth_rewrite 4 [←List.singleton_append]
            nth_rewrite 5 [←List.singleton_append]
            nth_rewrite 6 [←List.singleton_append]
            simp only [← List.append_assoc]
            have : 6 = ([PUSH (pre.length + b.compile.length + 4)] ++ [JUMPI] ++
                      [PUSH
                          (pre.length + b.compile.length +
                              (compileOffset (pre.length + b.compile.length + 4) c1).length +
                            6)] ++
                    [JUMP] ++
                [PUSH
                    (pre.length + b.compile.length + (compileOffset (pre.length + b.compile.length + 4) c1).length +
                        (compileOffset
                            (pre.length + b.compile.length +
                                (compileOffset (pre.length + b.compile.length + 4) c1).length +
                              6)
                            c2).length +
                      8)] ++
              [JUMP]).length := by simp
            nth_rewrite 5 [this]
            nth_rewrite 3 [this]
            have : (pre ++ b.compile ++ [PUSH (pre.length + b.compile.length + 4)] ++ [JUMPI] ++
                      [PUSH
                          (pre.length + b.compile.length +
                              (compileOffset (pre.length + b.compile.length + 4) c1).length +
                            6)] ++
                    [JUMP] ++
                  compileOffset (pre.length + b.compile.length + 4) c1 ++
                [PUSH
                    (pre.length + b.compile.length + (compileOffset (pre.length + b.compile.length + 4) c1).length +
                        (compileOffset
                            (pre.length + b.compile.length +
                                (compileOffset (pre.length + b.compile.length + 4) c1).length +
                              6)
                            c2).length +
                      8)] ++
              [JUMP]).length = pre.length + b.compile.length + (compileOffset (pre.length + b.compile.length + 4) c1).length +
                ([PUSH (pre.length + b.compile.length + 4)] ++ [JUMPI] ++
                          [PUSH
                              (pre.length + b.compile.length +
                                  (compileOffset (pre.length + b.compile.length + 4) c1).length +
                                6)] ++
                        [JUMP] ++
                      [PUSH
                          (pre.length + b.compile.length +
                                (compileOffset (pre.length + b.compile.length + 4) c1).length +
                              (compileOffset
                                  (pre.length + b.compile.length +
                                      (compileOffset (pre.length + b.compile.length + 4) c1).length +
                                    6)
                                  c2).length +
                            8)] ++
                    [JUMP]).length := by grind
            rw [←this]
          · apply Reachable.trans (Reachable.step rfl)
            simp only [step, Except.instMonad, Except.bind, fetchInstr, List.append_assoc,
              List.cons_append, List.nil_append, List.length_append, List.length_cons,
              List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.add_lt_add_iff_left,
              Nat.add_lt_add_iff_right, Nat.lt_add_right_iff_pos, Nat.lt_add_left_iff_pos,
              Nat.zero_lt_succ, ↓reduceDIte, Nat.le_add_right, List.getElem_append_right,
              Nat.add_sub_cancel_left, List.getElem_cons_succ, Nat.le_refl, Nat.sub_self,
              List.getElem_cons_zero, replaceStackAndIncrPC, incrPC, stackPeek2, beq_iff_eq,
              gt_iff_lt]
            apply Reachable.step
            simp +arith [step, fetchInstr, replaceStackAndIncrPC, incrPC, stackPeek2, stackPeek1, replaceMemStackAndIncrPC]
            have : pre.length + b.compile.length +
              (compileOffset (pre.length + b.compile.length + 4) c1).length +
            (compileOffset
                (pre.length + b.compile.length + (compileOffset (pre.length + b.compile.length + 4) c1).length + 6)
                c2).length + 7 - pre.length = b.compile.length +
              (compileOffset (pre.length + b.compile.length + 4) c1).length +
            (compileOffset
                (pre.length + b.compile.length + (compileOffset (pre.length + b.compile.length + 4) c1).length + 6)
                c2).length + 7 := by omega
            simp only [this]
            simp +arith [List.getElem_cons, List.getElem_append]
            have : b.compile.length + (compileOffset (pre.length + b.compile.length + 4) c1).length +
                (compileOffset
                    (pre.length + b.compile.length + (compileOffset (pre.length + b.compile.length + 4) c1).length + 6)
                    c2).length + 7 -
              b.compile.length = (compileOffset (pre.length + b.compile.length + 4) c1).length +
                (compileOffset
                    (pre.length + b.compile.length + (compileOffset (pre.length + b.compile.length + 4) c1).length + 6)
                    c2).length + 7 := by omega
            simp +arith [this]
            have : (compileOffset (pre.length + b.compile.length + 4) c1).length +
                (compileOffset
                    (pre.length + b.compile.length + (compileOffset (pre.length + b.compile.length + 4) c1).length + 6)
                    c2).length + 3 -
              (compileOffset (pre.length + b.compile.length + 4) c1).length = (compileOffset
                    (pre.length + b.compile.length + (compileOffset (pre.length + b.compile.length + 4) c1).length + 6)
                    c2).length + 3 := by omega
            simp +arith [this]
    | CWhile b c ih =>
      simp only [compileOffset, List.append_assoc, List.cons_append, List.nil_append, List.length_append, List.length_cons,
        List.length_nil, Nat.zero_add, Nat.reduceAdd]
      apply Reachable.trans (BExp.compileCorrectAux b)
      generalize eq : ⟨{ while ↑b do ↑c od }⟩ = loop at h
      induction h with
      | EWhileFalse hx =>
          cases eq
          simp only [Bool.toValue, hx, List.length_append]
          apply Reachable.trans (Reachable.step rfl)
          simp only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append,
            List.length_cons, Nat.add_lt_add_iff_left, Nat.lt_add_right_iff_pos,
            Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, ↓reduceDIte, Nat.le_add_right,
            List.getElem_append_right, Nat.add_sub_cancel_left, Nat.le_refl, Nat.sub_self,
            List.getElem_cons_zero, replaceStackAndIncrPC, incrPC, stackPeek2, beq_iff_eq,
            gt_iff_lt]
          apply Reachable.trans (Reachable.step rfl)
          simp +arith only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append,
            List.length_cons, ↓reduceDIte, List.getElem_append_right, replaceStackAndIncrPC, incrPC,
            stackPeek2, Nat.zero_add, Nat.le_add_left, Nat.sub_eq_zero_of_le, Nat.zero_mul,
            beq_iff_eq, Nat.right_eq_add, Nat.add_eq_zero_iff, List.length_eq_zero_iff,
            reduceCtorEq, and_false, ↓reduceIte, gt_iff_lt, Nat.lt_irrefl]
          have : pre.length + b.compile.length + 1 - pre.length = b.compile.length + 1 := by omega
          simp only [this, Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left,
            List.getElem_cons_succ, List.getElem_cons_zero]
          apply Reachable.trans (Reachable.step rfl)
          simp +arith only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append,
            List.length_cons, ↓reduceDIte, List.getElem_append_right, replaceStackAndIncrPC, incrPC,
            stackPeek2, beq_iff_eq, gt_iff_lt]
          have : pre.length + b.compile.length + 2 - pre.length = b.compile.length + 2 := by omega
          simp only [this, Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left,
            List.getElem_cons_succ, List.getElem_cons_zero]
          apply Reachable.step
          simp +arith only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append,
            List.length_cons, ↓reduceDIte, List.getElem_append_right, replaceStackAndIncrPC, incrPC,
            stackPeek1, stackPeek2, beq_iff_eq, Nat.add_eq_zero_iff, List.length_eq_zero_iff,
            reduceCtorEq, and_false, ↓reduceIte, gt_iff_lt]
          have : pre.length + b.compile.length + 3 - pre.length = b.compile.length + 3 := by omega
          simp [this]
      | EWhileTrue hx c' hn ihh1 ihh2 =>
        cases eq
        simp only [Bool.toValue, hx, List.length_append]
        apply Reachable.trans (Reachable.step rfl)
        simp only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append, List.length_cons,
          Nat.add_lt_add_iff_left, Nat.lt_add_right_iff_pos, Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, ↓reduceDIte,
          Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left, Nat.le_refl, Nat.sub_self,
          List.getElem_cons_zero, replaceStackAndIncrPC, incrPC, stackPeek2, beq_iff_eq, gt_iff_lt]
        apply Reachable.trans (Reachable.step rfl)
        simp +arith only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append,
          List.length_cons, ↓reduceDIte, List.getElem_append_right, replaceStackAndIncrPC, incrPC,
          stackPeek2, Nat.le_add_left, Nat.sub_eq_zero_of_le, Nat.one_mul, beq_iff_eq,
          Nat.right_eq_add, Nat.add_eq_zero_iff, List.length_eq_zero_iff, reduceCtorEq, and_false,
          ↓reduceIte, gt_iff_lt, Nat.lt_add_one]
        have : pre.length + b.compile.length + 1 - pre.length = b.compile.length + 1 := by omega
        simp only [this, Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left,
          List.getElem_cons_succ, List.getElem_cons_zero]
        convert Reachable.trans (ih _ _ _ _ _ c') _ using 1
        · rw [←List.append_assoc]
          rw [←List.singleton_append]
          nth_rewrite 2 [←List.singleton_append]
          nth_rewrite 3 [←List.singleton_append]
          nth_rewrite 4 [←List.singleton_append]
          have : 4 = ([PUSH (pre.length + b.compile.length + 4)] ++ [JUMPI] ++
              [PUSH
                  (pre.length + b.compile.length + (compileOffset (pre.length + b.compile.length + 4) c).length +
                    6)] ++
            [JUMP]).length := by simp
          nth_rewrite 3 [this]
          nth_rewrite 5 [this]
          repeat rw [←List.length_append]
          repeat rw [←List.append_assoc]
        · simp +arith only [List.length_append, List.append_assoc, List.cons_append,
          List.nil_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
          apply Reachable.trans (Reachable.step rfl)
          simp +arith only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append,
            List.length_cons, ↓reduceDIte, List.getElem_append_right, replaceStackAndIncrPC, incrPC,
            stackPeek2, beq_iff_eq, gt_iff_lt]
          have s1: ∀n, pre.length + b.compile.length +
            (compileOffset (pre.length + b.compile.length + 4) c).length + n - pre.length
              = b.compile.length +
            (compileOffset (pre.length + b.compile.length + 4) c).length + n := by omega
          simp +arith only [s1, List.getElem_append_right]
          have s2 : ∀n, b.compile.length + (compileOffset (pre.length + b.compile.length + 4) c).length + n -
            b.compile.length = (compileOffset (pre.length + b.compile.length + 4) c).length + n := by omega
          simp +arith only [s2, List.getElem_cons_succ, Nat.le_refl, List.getElem_append_right,
            Nat.sub_self, List.getElem_cons_zero]
          apply Reachable.trans (Reachable.step rfl)
          simp +arith only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append,
            List.length_cons, ↓reduceDIte, List.getElem_append_right, replaceStackAndIncrPC, incrPC,
            stackPeek1, stackPeek2, beq_iff_eq, List.length_eq_zero_iff, gt_iff_lt]
          simp +arith only [s1, List.getElem_append_right]
          simp +arith only [s2, List.getElem_cons_succ, Nat.le_add_right, List.getElem_append_right,
            Nat.add_sub_cancel_left, List.getElem_cons_zero]
          apply Reachable.trans (BExp.compileCorrectAux b)
          simp +arith only [Bool.toValue, List.length_append, forall_const] at ihh2
          simp only [Bool.toValue, List.length_append]
          exact ihh2
      | _ => contradiction

lemma Com.compileCorrectAux2 (pgm σ σ' stack) (h : σ =[pgm]=> σ') :
  Reachable
    (.ok ⟨pgm.compile, stack, σ, 0⟩)
    (.ok ⟨pgm.compile, stack, σ', pgm.compile.length⟩) := by
    rw [Com.compile]
    have hx := Com.compileCorrectAux _ σ σ' stack [] [STOP] h
    simp only [List.length_nil, List.nil_append] at hx
    apply Reachable.trans hx
    apply Reachable.step
    simp only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.lt_add_one, ↓reduceDIte, Nat.le_refl, List.getElem_append_right, Nat.sub_self,
    List.getElem_cons_zero, replaceStackAndIncrPC, incrPC, stackPeek1, stackPeek2, beq_iff_eq, gt_iff_lt]

/- With these lemmas on hand, proving correctness of compilation for {`AExp`, `BExp`, whole programs} is an easy consequence.
  I kept the proofs in full, they do not need to be filled out.
  Try to work out their reasoning and understand how the lemmas come into play!

  Important: `executeLemma` plays a crucial role here, which is marked as a
  hard optional exercise in `Lemmas.lean`. Why is it so important?
-/

theorem AExp.compileCorrect (a : AExp) (σ stack) :
  ∃ fuel : ℕ,
    execute fuel ⟨a.compile, stack, σ, 0⟩ =
      .ok ⟨a.compile, a.eval σ :: stack, σ, a.compile.length⟩ := by
  apply executeLemma
  · have := AExp.compileCorrectAux (pre := []) (suf := []) (mem := σ) (stack := stack) a
    simp only [List.append_nil, List.nil_append, List.length_nil] at this
    apply this
  · simp only [isFinal]

theorem BExp.compileCorrect (b : BExp) (σ stack) :
  ∃ fuel : ℕ,
    execute fuel ⟨b.compile, stack, σ, 0⟩ =
      .ok ⟨b.compile, (b.eval σ).toValue :: stack, σ, b.compile.length⟩ := by
  apply executeLemma
  · have := BExp.compileCorrectAux (pre := []) (suf := []) (mem := σ) (stack := stack) b
    simp only [List.append_nil, List.nil_append, List.length_nil] at this
    apply this
  · simp only [isFinal]

theorem Com.compileCorrect (pgm σ σ' stack) (h : σ =[pgm]=> σ') :
  ∃ fuel : ℕ,
    execute fuel ⟨pgm.compile, stack, σ, 0⟩ = .ok ⟨pgm.compile, stack, σ', pgm.compile.length⟩ := by
  apply executeLemma
  · apply compileCorrectAux2
    assumption
  · simp only [isFinal]
