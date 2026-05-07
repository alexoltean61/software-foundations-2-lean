import SoftwareFoundations2.StackMachine.Semantics

/-
  All exercises in this file are optional, but they may be a very good exercise to get a grasp
  of the transition system we are compiling IMP to.
-/

-- When you use `simp` in this file,
-- all of the following definitions will automatically be unfolded:
attribute [local simp] step
attribute [local simp] replaceMemStackAndIncrPC
attribute [local simp] replaceStackAndIncrPC
attribute [local simp] incrPC
attribute [local simp] fetchInstr
attribute [local simp] stackPeek2
attribute [local simp] stackPeek1

lemma isErrorLemma {err st'} : ¬ Reachable (.error err) st' := by
  intros r
  generalize R : Except.error err = st at r
  induction r
  · cases R
  · rename_i h _
    rw [R] at h
    simp at h

lemma isOOFLemma {st} : ¬ Reachable st (.error .OutOfFuel) := by
  intros r
  generalize R : Except.error ExecutionException.OutOfFuel = st' at r
  induction r
  · rename_i μ st'' h
    simp only [step, fetchInstr, replaceStackAndIncrPC, incrPC, stackPeek1,
      replaceMemStackAndIncrPC, stackPeek2, beq_iff_eq, gt_iff_lt] at h
    by_cases pc_ok : μ.pc < μ.code.length
    · simp only [pc_ok, ↓reduceDIte] at h
      generalize m : μ.code[μ.pc] = c
      cases c
      · rw [m] at h
        simp only [bind, Except.bind] at h
        rw [← h] at R
        simp at R
      · rw [m] at h
        simp only [bind, Except.bind] at h
        rw [← h] at R
        simp at R
      · rw [m] at h
        simp only [bind, Except.bind] at h
        rw [← h] at R
        generalize s : μ.stack = stiva
        cases stiva
        · simp [s] at R
        · simp [s] at R
      · rw [m] at h
        simp only [bind, Except.bind] at h
        rw [← h] at R
        generalize s : μ.stack = stiva
        cases stiva
        · simp [s] at R
        · rename_i head tail
          generalize s' : tail = t
          cases t
          · rw [s'] at s
            simp [s] at R
          · rw [s'] at s
            simp [s] at R
      · rw [m] at h
        simp only [bind, Except.bind] at h
        rw [← h] at R
        generalize s : μ.stack = stiva
        cases stiva
        · simp [s] at R
        · rename_i head tail
          generalize s' : tail = t
          cases t
          · rw [s'] at s
            simp [s] at R
          · rw [s'] at s
            simp [s] at R
      · rw [m] at h
        simp only [bind, Except.bind] at h
        rw [← h] at R
        generalize s : μ.stack = stiva
        cases stiva
        · simp [s] at R
        · rename_i head tail
          generalize s' : tail = t
          cases t
          · rw [s'] at s
            simp [s] at R
          · rw [s'] at s
            simp [s] at R
      · rw [m] at h
        simp only [bind, Except.bind] at h
        rw [← h] at R
        generalize s : μ.stack = stiva
        cases stiva
        · simp [s] at R
        · rename_i head tail
          generalize s' : tail = t
          cases t
          · rw [s'] at s
            simp [s] at R
          · rw [s'] at s
            simp [s] at R
            rename_i head' _
            by_cases h'h : head' = head
            · simp [h'h] at R
            · simp [h'h] at R
      · rw [m] at h
        simp only [bind, Except.bind] at h
        rw [← h] at R
        generalize s : μ.stack = stiva
        cases stiva
        · simp [s] at R
        · rename_i head tail
          generalize s' : tail = t
          cases t
          · rw [s'] at s
            simp [s] at R
          · rw [s'] at s
            simp [s] at R
            rename_i head' _
            by_cases h'h : head' ≤ head
            · simp [h'h] at R
            · simp [h'h] at R
      · rw [m] at h
        simp only [bind, Except.bind] at h
        rw [← h] at R
        generalize s : μ.stack = stiva
        cases stiva
        · simp [s] at R
        · simp [s] at R
          rename_i head _
          by_cases h0 : head = 0
          · simp [h0] at R
          · simp [h0] at R
      · rw [m, ← R] at h
        simp only [bind, Except.bind] at h
        generalize s : μ.stack = stiva
        cases stiva
        · simp [s] at h
        · simp [s] at h
      · rw [m, ← R] at h
        simp only [bind, Except.bind] at h
        generalize s : μ.stack = stiva
        cases stiva
        · simp [s] at h
        · rename_i head tail
          generalize s' : tail = t
          cases t
          · rw [s'] at s
            simp [s] at h
          · rw [s'] at s
            simp [s] at h
            rename_i head' _
            by_cases h0 : 0 < head'
            · simp [h0] at h
            · simp [h0] at h
      · rw [m, ← R] at h
        simp [bind, Except.bind] at h
      · rw [m, ← R] at h
        simp [bind, Except.bind] at h
    · simp [pc_ok, bind, Except.bind, ←R] at h
  · rename_i ih
    exact ih R

lemma isFinalStepLemma {μ st} (h : isFinal (.ok μ)) :
    step μ = st → isError st := by
  intros s
  unfold isError
  cases st
  · simp
  · simp
    simp at s
    unfold isFinal at h
    simp at h
    simp [h] at s
    simp [bind, Except.bind] at s

lemma isFinalLemma {st st'} (h : isFinal st) :
    Reachable st st' → isError st' := by
    intros r
    induction r
    · rename_i μ st'' stp
      unfold isFinal at h
      simp only at h
      simp only [step, bind, Except.bind, fetchInstr, h, Nat.lt_irrefl, ↓reduceDIte] at stp
      rw [←stp]
      unfold isError
      simp only
    · rename_i st1 st2 sti st1i sti2 ih0 ih1
      specialize ih0 h
      cases sti
      · exact isErrorLemma.elim sti2
      · unfold isError at ih0
        simp at ih0

lemma executeFinal {μ st fuel} (h : isFinal (.ok μ)) :
    execute fuel μ = st → st = .ok μ := by
  intros ef
  unfold execute at ef
  simp [h] at ef
  simp [ef]

lemma executeExtend {μ μ' fuel} (h : step μ = .ok μ') :
    execute (fuel + 1) μ = execute fuel μ' := by
  conv in execute (fuel + 1) μ => {unfold execute}
  by_cases h' : isFinal (Except.ok μ)
  · simp only [h', ↓reduceIte]
    unfold isFinal at h'
    simp at h'
    simp [h', bind, Except.bind] at h
  · simp only [h', ↓reduceIte, h]

lemma executeStepFinal {μ st} (h1 : isFinal st) (h2 : step μ = st) :
    execute 1 μ = st := by
  cases st
  · simp [isFinal] at h1
  · rename_i μ'
    unfold execute
    by_cases h : isFinal (Except.ok μ)
    · simp [h]
      unfold isFinal at h
      simp at h
      simp [h, bind, Except.bind] at h2
    · simp only [h, reduceIte, h2, execute, h1]

lemma execTrans {μ μ'} (h : Reachable (.ok μ) (.ok μ')) :
    ∃ k : ℕ, ∀ n : ℕ, execute (n + k) μ = execute n μ' := by
  generalize M : Except.ok μ = m at h
  generalize M' : Except.ok μ' = m' at h
  induction h generalizing μ μ'
  · rename_i μ'' st stp
    simp only [← M'] at stp
    simp at M
    simp only [←M] at stp
    use 1
    intros n
    conv in (execute (n + 1) μ) => unfold execute
    simp only [stp]
    simp only [ite_eq_right_iff]
    intros h
    unfold isFinal at h
    simp at h
    simp [h, bind, Except.bind] at stp
  · rename_i st1 st3 st2 r12 r23 ih12 ih23
    cases st2
    · apply (isErrorLemma r23).elim
    · rename_i μ''
      simp only [Except.ok.injEq, forall_eq_apply_imp_iff, ←M, forall_eq] at ih12
      simp only [Except.ok.injEq, forall_eq_apply_imp_iff, ←M', forall_eq] at ih23
      cases ih12 with
      | intro k1 h1 =>
        cases ih23 with
        | intro k2 h2 =>
          use k2 + k1
          intros n
          rw [←Nat.add_assoc]
          simp only [h1, h2]

/-- Hard exercise, you will likely need the lemmas above,
    and possibly additional intermediary results. -/
lemma executeLemma {μ st} (h1 : Reachable (.ok μ) st) (h2 : isFinal st) :
    ∃ fuel : ℕ, execute fuel μ = st := by
  cases st
  · simp [isFinal] at h2
  · rename_i μ'
    have h := execTrans h1
    cases h with
    | intro k h =>
      use k
      specialize h 0
      simp only [Nat.zero_add] at h
      have e : execute 0 μ' = Except.ok μ' := by
        simp [execute, h2]
      rw [e] at h
      exact h
