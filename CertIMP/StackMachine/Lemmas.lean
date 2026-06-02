import CertIMP.StackMachine.Semantics

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
  -- different structure: discharge the `step` case with `simp at eq`, reuse the IH directly
  intro h
  generalize eq : (Except.error err : ExecutionState) = st at h
  induction h with
  | step _ => simp at eq
  | trans _ _ ih1 _ => exact ih1 eq

lemma isOOFLemma {st} : ¬ Reachable st (.error .OutOfFuel) := by
  -- different structure: `subst` in the step case, reuse the IH directly in `trans`
  intro h
  generalize eq : (Except.error ExecutionException.OutOfFuel : ExecutionState) = st' at h
  induction h with
  | @step μ _ hstep =>
    subst eq
    simp [step, Bind.bind, Except.bind] at hstep
    aesop
  | trans _ _ _ ih2 => exact ih2 eq

lemma isFinalStepLemma {μ st} (h : isFinal (.ok μ)) :
    step μ = st → isError st := by
  -- different structure: `subst` the step result first, then compute that `step` errors out
  intro hstep
  subst hstep
  rw [isFinal] at h
  simp [step, bind, Except.bind, fetchInstr, h, isError]

lemma isFinalLemma {st st'} (h : isFinal st) :
    Reachable st st' → isError st' := by
  -- different structure: name the IH result, then case on the intermediate state
  intro hr
  induction hr with
  | @step μ st'' hx => exact isFinalStepLemma h hx
  | @trans _ _ st'' _ s2 ih1 _ =>
    have herr := ih1 h
    cases st'' with
    | ok => simp [isError] at herr
    | error e => exact absurd s2 isErrorLemma

lemma executeFinal {μ st fuel} (h : isFinal (.ok μ)) :
    execute fuel μ = st → st = .ok μ := by
  -- different structure: `subst` the result, then unfold `execute` once
  intro h1
  subst h1
  rw [execute.eq_def]
  simp [h]

lemma executeExtend {μ μ' fuel} (h : step μ = .ok μ') :
    execute (fuel + 1) μ = execute fuel μ' := by
  -- different structure: a successful step means μ is not final, so unfold `execute` once
  have hnf : ¬ isFinal (.ok μ) := fun hf => by
    have he := isFinalStepLemma hf h
    simp [isError] at he
  conv_lhs => rw [execute.eq_def]
  rw [if_neg hnf, h]

lemma executeStepFinal {μ st} (h1 : isFinal st) (h2 : step μ = st) :
    execute 1 μ = st := by
  -- different structure: derive not-final from h1+h2, then unfold `execute 1` then `execute 0`
  have hnf : ¬ isFinal (.ok μ) := by
    intro hf
    have hi := isFinalStepLemma hf h2
    cases st with
    | ok => simp [isError] at hi
    | error => simp [isFinal] at h1
  conv_lhs => rw [execute.eq_def]
  rw [if_neg hnf, h2]
  cases st with
  | ok μ' =>
      change execute 0 μ' = .ok μ'
      rw [execute.eq_def, if_pos h1]
  | error e => simp [isFinal] at h1

lemma executeLemmaAux {n : Nat} {μ μ' : MachineState} (h : Reachable (.ok μ) (.ok μ'))
  : ∃m, execute m μ = execute n μ' := by
  generalize eq1 : Except.ok μ = st at h
  generalize eq2 : Except.ok μ' = st' at h
  induction h generalizing n μ μ' with
  -- different structure: term-mode witnesses (`⟨·,·⟩`) and `▸` for the final chain
  | step hs =>
    cases eq1
    cases eq2
    exact ⟨n + 1, executeExtend hs⟩
  | @trans _ _ sti _ _ ih1 ih2 =>
    cases eq1
    cases eq2
    simp only [Except.ok.injEq, forall_eq_apply_imp_iff] at *
    cases sti with
    | error x =>
      have := @isErrorLemma x (Except.ok μ')
      contradiction
    | ok μi =>
      specialize @ih2 n μi rfl
      obtain ⟨m2, hm2⟩ := ih2
      specialize @ih1 m2 μ μi rfl rfl
      obtain ⟨m1, hm1⟩ := ih1
      exact ⟨m1, hm2 ▸ hm1⟩

/-- Hard exercise, you will likely need the lemmas above,
    and possibly additional intermediary results. -/
lemma executeLemma {μ st} (h1 : Reachable (.ok μ) st) (h2 : isFinal st) :
    ∃ fuel : ℕ, execute fuel μ = st := by
  -- different structure: case on st, reuse executeLemmaAux at fuel 0, term-mode witness
  cases st with
  | error e => simp [isFinal] at h2
  | ok μx =>
    obtain ⟨m, hm⟩ := executeLemmaAux (n := 0) h1
    refine ⟨m, ?_⟩
    rw [hm, execute.eq_def, if_pos h2]
