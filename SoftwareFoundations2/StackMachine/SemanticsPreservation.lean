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
      simp only [compile, List.cons_append, List.nil_append, eval, List.length_append,
        List.length_cons, List.length_nil, Nat.zero_add]
      apply Reachable.step
      simp [step, fetchInstr, replaceStackAndIncrPC, incrPC]
    | AId x =>
      simp only [compile, List.cons_append, List.nil_append, eval, List.length_append,
        List.length_cons, List.length_nil, Nat.zero_add]
      apply Reachable.step
      simp [step, fetchInstr, replaceStackAndIncrPC, incrPC]
    | _ a b ih1 ih2 =>
      simp only [compile, List.append_assoc, List.cons_append, List.nil_append, eval,
        List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      apply Reachable.trans
      · apply ih1
      · rw [← List.append_assoc]
        have h : Reachable
          (Except.ok
            { code := pre ++ a.compile ++ (b.compile ++ ADD :: suf), stack := eval mem a :: stack, mem := mem,
              pc := (pre ++ a.compile).length })
          (Except.ok
            { code := pre ++ a.compile ++ (b.compile ++ ADD :: suf), stack := eval mem b :: (eval mem a) :: stack, mem := mem,
              pc := pre.length + (a.compile.length + (b.compile.length)) }) := by
              simp only [List.length_append] at ih2
              rw [← Nat.add_assoc, ← List.length_append]
              apply ih2
        apply Reachable.trans
        · simp only [List.length_append] at ih2
          apply ih2
        · apply Reachable.step
          · have h {a b : Nat} : a < a + (b + 1) := by
              simp only [Nat.lt_add_right_iff_pos, Nat.zero_lt_succ]
            simp only [step, fetchInstr, List.length_append, List.length_cons, List.append_assoc, Nat.add_assoc, Nat.add_lt_add_iff_left, Nat.lt_add_right_iff_pos, Nat.zero_lt_succ, Except.instMonad, Except.bind, ↓reduceDIte, Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left, Nat.le_refl, Nat.sub_self, List.getElem_cons_zero, beq_iff_eq, gt_iff_lt, stackPeek2, replaceStackAndIncrPC, incrPC, Nat.add_assoc]

lemma BExp.compileCorrectAux {pre suf stack mem} (b : BExp) :
  Reachable
    (.ok ⟨pre ++ (b.compile ++ suf), stack, mem, pre.length⟩)
    (.ok ⟨pre ++ (b.compile ++ suf), (b.eval mem).toValue :: stack, mem, (pre ++ b.compile).length⟩) := by
    induction b generalizing pre suf stack with
    | BTrue =>
      apply Reachable.step
      simp [step, fetchInstr, compile, replaceStackAndIncrPC, incrPC]
    | BFalse =>
      apply Reachable.step
      simp [step, fetchInstr, compile, replaceStackAndIncrPC, incrPC]
    | BEq a b =>
      simp only [compile, List.append_assoc, List.cons_append, List.nil_append, Bool.toValue, eval,
        List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      apply Reachable.trans
      · apply AExp.compileCorrectAux
      · apply Reachable.trans
        · rw [← List.append_assoc]
          apply AExp.compileCorrectAux
        · apply Reachable.step
          simp [step, fetchInstr, stackPeek2, replaceStackAndIncrPC, incrPC, Nat.add_assoc]
          by_cases h : AExp.eval mem a = AExp.eval mem b
          · simp [h]
          · simp [h]
            have h' : (AExp.eval mem a == AExp.eval mem b) = false := by simp [h]
            simp [h']
    | BNeq a b =>
      simp only [compile, List.append_assoc, List.cons_append, List.nil_append, Bool.toValue, eval, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      apply Reachable.trans
      · apply AExp.compileCorrectAux
      · apply Reachable.trans
        · rw [← List.append_assoc]
          apply AExp.compileCorrectAux
        · apply Reachable.trans
          · apply Reachable.step
            simp [step, fetchInstr, stackPeek2]
            rfl
          · simp only [Nat.reduceAdd]
            by_cases h : AExp.eval mem a = AExp.eval mem b
            · simp only [h, ↓reduceIte, bne_self_eq_false]
              apply Reachable.step
              simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, Nat.add_assoc, stackPeek1]
            · simp only [h, ↓reduceIte]
              apply Reachable.step
              have h' : AExp.eval mem a != AExp.eval mem b := by simp [h]
              simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, Nat.add_assoc, stackPeek1, h']
    | BLe a b =>
      simp only [compile, List.append_assoc, List.cons_append, List.nil_append, Bool.toValue, eval, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      apply Reachable.trans
      · apply AExp.compileCorrectAux
      · apply Reachable.trans
        · rw [← List.append_assoc]
          apply AExp.compileCorrectAux
        · apply Reachable.step
          simp [step, fetchInstr, stackPeek2]
          by_cases h : AExp.eval mem a ≤ AExp.eval mem b
          · simp only [h, ↓reduceIte, decide_true, replaceStackAndIncrPC, incrPC, Nat.add_assoc]
          · simp only [h, ↓reduceIte, decide_false, replaceStackAndIncrPC, incrPC, Nat.add_assoc]
    | BGt a b =>
      simp only [compile, List.append_assoc, List.cons_append, List.nil_append, Bool.toValue, eval, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      apply Reachable.trans
      · apply AExp.compileCorrectAux
      · apply Reachable.trans
        · rw [← List.append_assoc]
          apply AExp.compileCorrectAux
        · apply Reachable.trans
          · apply Reachable.step
            simp [step, fetchInstr, stackPeek2]
            rfl
          · simp only [Nat.reduceAdd]
            by_cases h : AExp.eval mem a ≤ AExp.eval mem b
            · simp only [h, ↓reduceIte, gt_iff_lt]
              apply Reachable.step
              simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, Nat.add_assoc, stackPeek1]
              have h' : ¬ (AExp.eval mem b < AExp.eval mem a) := by simp [h]
              simp only [h', decide_false]
            · simp only [h, ↓reduceIte, gt_iff_lt]
              apply Reachable.step
              have h' : AExp.eval mem b < AExp.eval mem a := by
                simp at h
                simp [h]
              simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, Nat.add_assoc, stackPeek1, h']
    | BNot b ih =>
      simp only [compile, List.append_assoc, List.cons_append, List.nil_append, Bool.toValue, eval, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      apply Reachable.trans
      · apply ih
      · apply Reachable.step
        simp [step, fetchInstr, stackPeek1]
        by_cases h : BExp.eval mem b
        · simp [h, replaceStackAndIncrPC, incrPC, Nat.add_assoc]
        · simp [h, replaceStackAndIncrPC, incrPC, Nat.add_assoc]
    | BAnd a b aih bih =>
      simp only [compile, List.append_assoc, List.cons_append, List.nil_append, Bool.toValue, eval, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      apply Reachable.trans
      · apply aih
      · rw [← List.append_assoc]
        apply Reachable.trans
        · apply bih
        · apply Reachable.step
          simp only [step, Except.instMonad, Except.bind, fetchInstr, List.append_assoc, List.length_append, List.length_cons, Nat.add_lt_add_iff_left, Nat.lt_add_right_iff_pos, Nat.zero_lt_succ, ↓reduceDIte, Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left, Nat.le_refl, Nat.sub_self, List.getElem_cons_zero, Bool.toValue, replaceStackAndIncrPC, incrPC, stackPeek2, beq_iff_eq, gt_iff_lt, Except.ok.injEq, MachineState.mk.injEq, List.cons.injEq, and_true, true_and, Nat.add_assoc]
          by_cases ea : eval mem a
          · simp [ea]
          · simp [ea]

/- For this proof, don't be set off if it becomes super technical and long.
   You can likely split the definition of Com.compileOffset into multiple sub-operations,
   and prove sub-lemmas for each sub-operation.
   But you don't have to; the naive way of proving this will likely suffice.
-/
lemma Com.compileCorrectAux (pgm σ σ' stack pre suf) (h : σ =[pgm]=> σ') :
  Reachable
    (.ok ⟨pre ++ pgm.compileOffset pre.length ++ suf, stack, σ, pre.length⟩)
    (.ok ⟨pre ++ pgm.compileOffset pre.length ++ suf, stack, σ', (pre ++ pgm.compileOffset pre.length).length⟩) := by
    induction pgm generalizing pre suf stack σ σ' with
    | CSkip =>
      simp only [compileOffset, List.append_assoc, List.cons_append, List.nil_append, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      apply Reachable.step
      simp [step, fetchInstr, incrPC]
      cases h
      rfl
    | CAsgn x a =>
      simp only [compileOffset, List.append_assoc, List.cons_append, List.nil_append, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      apply Reachable.trans
      · apply AExp.compileCorrectAux
      · rw [← List.append_assoc]
        apply Reachable.step
        simp only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append, List.append_assoc, List.length_cons, Nat.add_lt_add_iff_left, Nat.lt_add_right_iff_pos, Nat.zero_lt_succ, ↓reduceDIte, Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left, Nat.le_refl, Nat.sub_self, List.getElem_cons_zero, replaceStackAndIncrPC, incrPC, Nat.add_assoc, stackPeek1, replaceMemStackAndIncrPC, beq_iff_eq, gt_iff_lt, Except.ok.injEq, MachineState.mk.injEq, and_true, true_and]
        cases h
        rename_i n n_eval σ'σ
        rw [σ'σ, n_eval]
    | CSeq c1 c2 ih1 ih2 =>
      simp only [compileOffset, List.append_assoc, List.length_append]
      cases h
      rename_i σ'' h h'
      apply Reachable.trans
      · rw [← List.append_assoc]
        specialize ih1 σ σ'' stack pre (compileOffset (pre.length + (compileOffset pre.length c1).length) c2 ++ suf) h
        apply ih1
      · specialize ih2 σ'' σ' stack (pre ++ compileOffset pre.length c1) suf h'
        simp only [List.append_assoc, List.length_append]
        simp only [List.length_append, List.append_assoc] at ih2
        apply ih2
    | CIf b c1 c2 ih1 ih2 =>
      simp only [compileOffset, List.append_assoc, List.cons_append, List.nil_append, List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
      cases h
      · rename_i bi h
        apply Reachable.trans
        · apply BExp.compileCorrectAux
        · rw [← List.append_assoc]
          simp only [bi, List.append_assoc, Bool.toValue, List.length_append]
          apply Reachable.trans
          · apply Reachable.step
            simp [step, fetchInstr, replaceStackAndIncrPC, incrPC]
            rfl
          · apply Reachable.trans
            · apply Reachable.step
              simp only [step, Except.instMonad, Except.bind, fetchInstr, Nat.add_assoc, List.length_append, List.length_cons, Nat.reduceAdd, Nat.add_lt_add_iff_left, Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left, List.getElem_cons_succ, List.getElem_cons_zero, dite_eq_ite, beq_iff_eq, gt_iff_lt]
              rw [← Nat.add_assoc _ _ 6]
            · rw [← Nat.add_assoc _ _ 6]
              simp only [Nat.add_comm, Nat.add_assoc, stackPeek2, Nat.one_mul, Nat.lt_add_one, ↓reduceIte]
              rw [Nat.add_comm 6]
              simp only [Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, ↓reduceIte]
              specialize ih1 σ σ' stack (pre ++ b.compile ++ PUSH (pre.length + (b.compile.length + 4)) :: JUMPI :: (PUSH (pre.length + (b.compile.length + ((compileOffset (pre.length + (b.compile.length + 4)) c1).length + 6))) :: [JUMP])) (PUSH (pre.length + (b.compile.length + ((compileOffset (pre.length + (b.compile.length + 4)) c1).length + ((compileOffset (pre.length + (b.compile.length + ((compileOffset (pre.length + (b.compile.length + 4)) c1).length + 6))) c2).length + 8)))) :: JUMP :: (compileOffset (pre.length + (b.compile.length + ((compileOffset (pre.length + (b.compile.length + 4)) c1).length + 6))) c2 ++ PUSH (pre.length + (b.compile.length + ((compileOffset (pre.length + (b.compile.length + 4)) c1).length + ((compileOffset (pre.length + (b.compile.length + ((compileOffset (pre.length + (b.compile.length + 4)) c1).length + 6))) c2).length + 8)))) :: JUMP :: suf)) h
              apply Reachable.trans
              · simp only [List.append_assoc, List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append] at ih1
                apply ih1
              · simp only [Nat.add_assoc, Nat.reduceAdd]
                apply Reachable.trans
                · apply Reachable.step
                  simp [step, fetchInstr, replaceStackAndIncrPC, incrPC]
                  rfl
                · apply Reachable.step
                  simp only [step, Except.instMonad, Except.bind, fetchInstr, Nat.add_assoc, Nat.reduceAdd, List.length_append, List.length_cons, Nat.add_lt_add_iff_left, Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left, List.getElem_cons_succ, List.getElem_cons_zero, dite_eq_ite, beq_iff_eq, gt_iff_lt]
                  rw [← Nat.add_assoc _ _ 8]
                  simp only [Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, ↓reduceIte, stackPeek1, Except.ok.injEq, MachineState.mk.injEq, Nat.add_left_cancel_iff, true_and]
                  repeat rw [← Nat.add_assoc _ 1]
                  simp only [Nat.reduceAdd]
                  rw [Nat.add_assoc (compileOffset (pre.length + (b.compile.length + 4)) c1).length 1 1]
                  simp only [Nat.reduceAdd]
                  repeat rw [Nat.add_assoc]
                  rw [← Nat.add_assoc 2 2]
                  simp only [Nat.reduceAdd]
                  rw [← Nat.add_assoc _ 4, Nat.add_comm (compileOffset (pre.length + (b.compile.length + 4)) c1).length 4]
                  simp only [Nat.add_assoc]
                  rw [← Nat.add_assoc 4 4]
                  simp only [Nat.reduceAdd]
                  rw [Nat.add_comm 8, Nat.add_assoc _ _ 8]
      · rename_i bi h
        apply Reachable.trans
        · apply BExp.compileCorrectAux
        · rw [← List.append_assoc]
          simp only [bi, List.append_assoc, Bool.toValue, List.length_append]
          apply Reachable.trans
          · apply Reachable.step
            simp [step, fetchInstr, replaceStackAndIncrPC, incrPC]
            rfl
          · apply Reachable.trans
            · apply Reachable.step
              simp only [step, Except.instMonad, Except.bind, fetchInstr, Nat.add_assoc, List.length_append, List.length_cons, Nat.reduceAdd, Nat.add_lt_add_iff_left, Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left, List.getElem_cons_succ, List.getElem_cons_zero, dite_eq_ite, beq_iff_eq, gt_iff_lt]
              rewrite [← Nat.add_assoc _ _ 8, ← Nat.add_assoc _ _ 8]
              simp only [Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, ↓reduceIte, stackPeek2, Nat.lt_irrefl, replaceStackAndIncrPC, incrPC]
              rewrite [Nat.add_assoc, Nat.add_assoc]
              simp only [Nat.reduceAdd]
              rfl
            · apply Reachable.trans
              · apply Reachable.step
                simp only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append, List.length_cons, Nat.add_lt_add_iff_left, Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, ↓reduceDIte, Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left, List.getElem_cons_succ, List.getElem_cons_zero, replaceStackAndIncrPC, incrPC, beq_iff_eq, gt_iff_lt]
                rewrite [Nat.add_assoc, Nat.add_assoc]
                simp only [Nat.reduceAdd]
                rfl
              · apply Reachable.trans
                · apply Reachable.step
                  simp [step, fetchInstr, stackPeek1]
                  rfl
                · apply Reachable.trans
                  · specialize ih2 σ σ' stack (pre ++ (b.compile ++ PUSH (pre.length + (b.compile.length + 4)) :: JUMPI :: PUSH (pre.length + (b.compile.length + ((compileOffset (pre.length + (b.compile.length + 4)) c1).length + 6))) :: JUMP :: (compileOffset (pre.length + (b.compile.length + 4)) c1 ++ PUSH (pre.length + (b.compile.length + ((compileOffset (pre.length + (b.compile.length + 4)) c1).length + ((compileOffset (pre.length + (b.compile.length + ((compileOffset (pre.length + (b.compile.length + 4)) c1).length + 6))) c2).length + 8)))) :: [JUMP]))) (PUSH (pre.length + (b.compile.length + ((compileOffset (pre.length + (b.compile.length + 4)) c1).length + ((compileOffset (pre.length + (b.compile.length + ((compileOffset (pre.length + (b.compile.length + 4)) c1).length + 6))) c2).length + 8)))) :: JUMP :: suf) h
                    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, List.append_assoc, List.cons_append, List.nil_append] at ih2
                    apply ih2
                  · apply Reachable.trans
                    · apply Reachable.step
                      simp [step, fetchInstr, replaceStackAndIncrPC, incrPC]
                      simp [Nat.add_assoc]
                      rfl
                    · apply Reachable.step
                      simp only [step, Except.instMonad, Except.bind, fetchInstr,
                        List.length_append, List.length_cons, Nat.add_lt_add_iff_left,
                        Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left,
                        beq_iff_eq, gt_iff_lt]
                      simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_lt_add_iff_left, Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, ↓reduceDIte]
                      simp only [Nat.add_comm]
                      rw [← Nat.add_assoc]
                      rw [← Nat.add_assoc]
                      rw [← Nat.add_assoc]
                      let a : Nat := (pre.length + b.compile.length + 4)
                      have h' : a = (pre.length + b.compile.length + 4) := by
                        unfold a
                        rfl
                      rw [← h']
                      let c := compileOffset a c1
                      have h'' : c = compileOffset a c1 := by
                        unfold c
                        rfl
                      rw [← h'']
                      let d := (pre.length + b.compile.length + c.length + 6)
                      have h''' : d = (pre.length + b.compile.length + c.length + 6) := by
                        unfold d
                        rfl
                      rw [← h''']
                      let e := (compileOffset d c2)
                      have h'''' : e = (compileOffset d c2) := by
                        unfold e
                        rfl
                      rw [← h'''']
                      simp_rw [← Nat.add_assoc]
                      simp only [List.getElem_cons_succ]
                      simp_rw [Nat.add_assoc, Nat.add_comm]
                      simp only [Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left]
                      simp_rw [Nat.add_comm 3 e.length]
                      simp only [List.getElem_cons_succ, Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left, List.getElem_cons_zero, stackPeek1]
    | CWhile b c ih =>
      generalize W : ⟨{ while ↑b do ↑c od }⟩ = loop
      rw [W] at h
      induction h with
      | EWhileFalse =>
        rename_i σ' b' c' bf
        simp only [CWhile.injEq] at W
        rcases W with ⟨bb', cc'⟩
        simp only [compileOffset, List.append_assoc, List.cons_append, List.nil_append, List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
        apply Reachable.trans
        · apply BExp.compileCorrectAux
        · apply Reachable.trans
          · apply Reachable.step
            simp [step, fetchInstr, replaceStackAndIncrPC, incrPC]
            rfl
          · simp only [bf]
            apply Reachable.trans
            · apply Reachable.step
              simp only [step, Except.instMonad, Except.bind, fetchInstr, Nat.add_assoc, List.length_append, List.length_cons, Nat.reduceAdd, Nat.add_lt_add_iff_left, Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left, List.getElem_cons_succ, List.getElem_cons_zero, dite_eq_ite, beq_iff_eq, gt_iff_lt]
              rewrite [← Nat.add_assoc _ _ 6]
              simp [stackPeek2, replaceStackAndIncrPC, incrPC]
              rfl
            · apply Reachable.trans
              · apply Reachable.step
                simp only [step, Except.instMonad, Except.bind, fetchInstr, Nat.add_assoc, Nat.reduceAdd, List.length_append, List.length_cons, Nat.add_lt_add_iff_left, Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left, List.getElem_cons_succ, List.getElem_cons_zero, dite_eq_ite, beq_iff_eq, gt_iff_lt]
                rewrite [← Nat.add_assoc _ _ 6]
                simp only [Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, ↓reduceIte]
                rfl
              · apply Reachable.step
                simp only [step, Except.instMonad, Except.bind, fetchInstr, replaceStackAndIncrPC, incrPC, Nat.add_assoc, Nat.reduceAdd, List.length_append, List.length_cons, Nat.add_lt_add_iff_left, Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left, List.getElem_cons_succ, List.getElem_cons_zero, dite_eq_ite, beq_iff_eq, gt_iff_lt]
                rewrite [← Nat.add_assoc _ _ 6]
                simp only [Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, ↓reduceIte, stackPeek1]
      | EWhileTrue =>
        rename_i s c' s' b' s'' b't ss' s's'' _ ih1
        specialize ih1 W
        simp only [CWhile.injEq] at W
        rcases W with ⟨bb', cc'⟩
        apply Reachable.trans
        · apply Reachable.trans
          · simp only [compileOffset, List.append_assoc]
            apply BExp.compileCorrectAux
          · apply Reachable.trans
            · apply Reachable.step
              simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, b't]
              rfl
            · apply Reachable.trans
              · apply Reachable.step
                simp only [step, Except.instMonad, Except.bind, fetchInstr, Nat.add_assoc, List.length_append, List.length_cons, Nat.reduceAdd, Nat.add_lt_add_iff_left, Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left, List.getElem_cons_succ, List.getElem_cons_zero, dite_eq_ite, beq_iff_eq, gt_iff_lt]
                rewrite [← Nat.add_assoc]
                simp only [Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, ↓reduceIte, stackPeek2, Nat.lt_add_one]
                rfl
              · apply Reachable.trans
                · rw [cc'] at ih
                  specialize ih s s' stack (pre ++ (b'.compile ++ PUSH (pre.length + (b'.compile.length + 4)) :: JUMPI :: PUSH (pre.length + (b'.compile.length + ((compileOffset (pre.length + (b'.compile.length + 4)) c').length + 6))) :: [JUMP])) (PUSH pre.length :: JUMP :: suf) ss'
                  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, List.append_assoc, List.cons_append, List.nil_append] at ih
                  apply ih
                · apply Reachable.trans
                  · apply Reachable.step
                    simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, Nat.add_assoc]
                    rfl
                  · apply Reachable.step
                    simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, Nat.add_assoc, stackPeek1]
                    rfl
        · simp only [compileOffset, Nat.add_assoc, List.append_assoc, List.cons_append, List.nil_append, List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at ih1
          simp only [compileOffset, Nat.add_assoc, List.append_assoc, List.cons_append, List.nil_append, List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
          apply ih1
      | _ => contradiction

lemma Com.compileCorrectAux2 (pgm σ σ' stack) (h : σ =[pgm]=> σ') :
  Reachable
    (.ok ⟨pgm.compile, stack, σ, 0⟩)
    (.ok ⟨pgm.compile, stack, σ', pgm.compile.length⟩) := by
    let h' := pgm.compileCorrectAux σ σ' stack [] [STOP] h
    simp only [List.length_nil, List.nil_append] at h'
    unfold compile
    apply Reachable.trans
    · apply h'
    · simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      apply Reachable.step
      simp [step, fetchInstr]

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
