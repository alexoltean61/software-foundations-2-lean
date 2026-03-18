import SoftwareFoundations2.Equiv.Def

open ComEval

variable {c c₁ c₂ c₃ : Com}
variable {b : BExp}

theorem aequiv_example : aexp⟨{ x - x }⟩ ≃ aexp⟨{ 0 }⟩ := by
  simp [aequiv, AExp.eval]

theorem bequiv_example : bexp⟨{ x - x == 0 }⟩ ≃ bexp⟨{ btrue }⟩ := by
  simp [bequiv, BExp.eval]

theorem skip_left : ⟨{ skip; ↑c }⟩ ≃ ⟨{ ↑c }⟩ := by
  -- WORKED IN CLASS
  intro σ σ'
  apply Iff.intro
  · intro h
    cases h with
    | ESeq h1 h2 =>
        cases h1
        exact h2
  · intro h
    apply ESeq ESkip
    exact h

theorem true_if (h : b ≃ bexp⟨{ btrue }⟩) :
  ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃ ⟨{ ↑c₁ }⟩ := by
  intro σ σ'
  apply Iff.intro
  · intro h1
    cases h1 with
    | EIfTrue _ _ => assumption
    | EIfFalse habs _ =>
        simp only [bequiv, BExp.eval] at h
        specialize h σ
        rw [h] at habs
        contradiction
  · intro h1
    apply EIfTrue _ h1
    apply h

theorem false_while (h : b ≃ bexp⟨{ bfalse }⟩) :
  ⟨{ while ↑b do ↑c od }⟩ ≃ ⟨{ skip }⟩ := by
  intro σ σ'
  apply Iff.intro
  · intro h1
    cases h1 with
    | EWhileFalse => exact ESkip
    | EWhileTrue habs =>
        simp only [bequiv, BExp.eval] at h
        specialize h σ
        rw [h] at habs
        contradiction
  · intro h2
    cases h2
    apply EWhileFalse
    apply h

theorem true_while_nonterm
  (h : b ≃ bexp⟨{ btrue }⟩) :
  ¬ σ =[ while ↑b do ↑c od ]=> σ' := by
  -- WORKED IN CLASS
  generalize eq : ⟨{ while ↑b do ↑c od }⟩ = loop
  intro habs
  induction habs with
  | EWhileFalse habs =>
      aesop
  | EWhileTrue htrue h1 h2 _ ih =>
      exact ih eq
  | _ => aesop

theorem loop_unrolling :
  ⟨{  while ↑b do ↑c od  }⟩ ≃
  ⟨{  if ↑b then
        ↑c;
        while ↑b do ↑c od;
      else
        skip;
      endif
  }⟩ := by
  -- WORKED IN CLASS
  intro σ σ'
  apply Iff.intro
  · intro h
    cases h with
    | EWhileTrue beval =>
        apply EIfTrue beval
        apply ESeq
        repeat assumption
    | EWhileFalse beval =>
        apply EIfFalse beval
        apply ESkip
  · intro h
    cases h with
    | EIfTrue beval h =>
        cases h
        apply EWhileTrue beval
        repeat assumption
    | EIfFalse beval h =>
        cases h
        apply EWhileFalse beval

theorem identity_assignment :
  ⟨{ x = x }⟩ ≃ ⟨{ skip }⟩ := by
  intro σ σ'
  apply Iff.intro
  · intro h
    cases h
    case EAsgn n eqn eqs
    · subst eqn
      simp only [AExp.eval, State.set_id] at eqs
      subst eqs
      exact ESkip
  · intro h
    cases h
    apply EAsgn rfl
    simp only [AExp.eval, State.set_id]

theorem skip_right : ⟨{ ↑c; skip }⟩ ≃ ⟨{ ↑c }⟩ := by
  -- FILL IN HERE
  intros σ σ'
  apply Iff.intro
  intros h
  cases h with
  | ESeq h1 h2 =>
    cases h2
    exact h1
  intros h
  apply ESeq
  · exact h
  apply ESkip


theorem false_if (h : b ≃ bexp⟨{ bfalse }⟩) :
  ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃ ⟨{ ↑c₂ }⟩ := by

-- afjlla
  intro σ σ'
  specialize h σ
  rw [BExp.eval] at h
  apply Iff.intro
  intros h1
  cases h1 with
  | EIfTrue h2 h3 =>
    rw [h] at h2
    contradiction
  | EIfFalse h2 h3 =>
    exact h3
  intros h1
  apply EIfFalse
  apply h
  exact h1


theorem swap_if_branches :
    ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃
    ⟨{ if !↑b then ↑c₂ else ↑c₁ endif }⟩ := by
  -- FILL IN HERE
  intro σ σ'
  apply Iff.intro
  intros h1
  cases h1 with
  | EIfTrue h2 h3 =>
    apply EIfFalse
    rw [BExp.eval, h2]
    trivial
    exact h3
  | EIfFalse h2 h3 =>
    apply EIfTrue
    rw [BExp.eval, h2]
    trivial
    exact h3
  intros h1
  cases h1 with
  | EIfTrue h2 h3 =>
    apply EIfFalse
    rw [BExp.eval] at h2
    rw [Bool.not_eq_eq_eq_not, Bool.not_true] at h2
    exact h2
    exact h3
  | EIfFalse h2 h3 =>
    apply EIfTrue
    rw [BExp.eval] at h2
    simp at h2
    exact h2
    exact h3


theorem true_while
  (h : b ≃ bexp⟨{ btrue }⟩) :
  ⟨{ while ↑b do ↑c od }⟩ ≃ ⟨{ while btrue do skip od }⟩ := by
  -- FILL IN HERE
  -- Hint: You'll want to use `true_while_nonterm` here.
  intros σ σ'
  apply Iff.intro
  intros h1
  apply true_while_nonterm at h
  contradiction
  intros h1
  apply true_while_nonterm at h

  sorry
  repeat trivial



theorem assign_aequiv
  (h : aexp⟨{ x }⟩ ≃ ↑a ) :
  ⟨{ x = ↑a }⟩ ≃ ⟨{ skip }⟩ := by
  intros σ σ'
  apply Iff.intro
  intros h1
  cases h1 with
  | EAsgn h2 h3 =>
    specialize h σ
    rw [← h] at h2
    rw [h2] at h3
    rw [AExp.eval] at h3
    rw [State.set_id] at h3
    rw [h3]
    apply ESkip
  intros h1
  cases h1 with
  | ESkip =>
    apply EAsgn
    trivial
    rw [← h]
    rw [AExp.eval]
    rw [State.set_id]

theorem equiv_refl : c ≃ c := by
  intros σ σ'
  rfl

@[trans]
theorem equiv_trans : c₁ ≃ c₂ → c₂ ≃ c₃ → c₁ ≃ c₃ := by
  -- FILL IN HERE
  intros h1
  intros h2
  intros σ σ'
  specialize h1 σ σ'
  specialize h2 σ σ'
  apply Iff.trans h1 h2

@[symm]
theorem equiv_symm : c₁ ≃ c₂ → c₂ ≃ c₁ := by
  -- FILL IN HERE
  intros h1
  intros σ σ'
  specialize h1 σ σ'
  apply Iff.symm
  exact h1

set_option warn.sorry false in
theorem equiv_congr_asgn {a₁ a₂ : AExp} (h : a₁ ≃ a₂) :
  ⟨{ ↑x = ↑a₁ }⟩ ≃ ⟨{ ↑x = ↑a₂ }⟩ := by
  -- FILL IN HERE (optional: PR will pass without it)
  intros σ σ'
  specialize h σ
  apply Iff.intro
  intros h1
  apply EAsgn
  rw [← h]
  cases h1 with
  | EAsgn h2 h3 =>
    rw [h2] at h3
    exact h3
  intros h1
  apply EAsgn
  rw [h]
  cases h1 with
  | EAsgn h2 h3 =>
    rw [h2] at h3
    assumption

set_option warn.sorry false in
theorem equiv_congr_seqL (h : c₁ ≃ c₁') :
  ⟨{ ↑c₁; ↑c₂ }⟩ ≃ ⟨{ ↑c₁'; ↑c₂ }⟩ := by
  -- FILL IN HERE (optional: PR will pass without it)
  intros σ σ'
  specialize h σ
  apply Iff.intro
  intros h1
  cases h1 with
  | @ESeq _ _ σ'' _ _ h2 h3 =>
    apply ESeq
    · specialize h σ''
      apply Iff.mp h
      exact h2
    apply h3
  intros h1
  cases h1 with
  | @ESeq _ _ σ'' _ _ h2 h3 =>
    apply ESeq
    · specialize h σ''
      apply Iff.mpr h
      apply h2
    apply h3

set_option warn.sorry false in
theorem equiv_congr_seqR (h : c₂ ≃ c₂') :
  ⟨{ ↑c₁; ↑c₂ }⟩ ≃ ⟨{ ↑c₁; ↑c₂' }⟩ := by
  sorry

set_option warn.sorry false in
theorem bequiv_congr_if (h : b ≃ b') :
  ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃ ⟨{ if ↑b' then ↑c₁ else ↑c₂ endif }⟩ := by
  -- FILL IN HERE (optional: PR will pass without it)
  intros σ σ'
  apply Iff.intro
  intros h1
  cases h1 with
  | EIfTrue h2 h3 =>
      apply EIfTrue
      · specialize h σ
        rw [h2] at h
        symm at h
        exact h
      exact h3
  | EIfFalse h2 h3 =>
      apply EIfFalse
      · specialize h σ
        rw [h2] at h
        symm
        exact h
      exact h3
  intros h1
  cases h1 with
  | EIfTrue h2 h3 =>
      apply EIfTrue
      · specialize h σ
        rw [h2] at h
        exact h
      exact h3
  | EIfFalse h2 h3 =>
      apply EIfFalse
      · specialize h σ
        rw [h2] at h
        exact h
      exact h3

set_option warn.sorry false in
theorem equiv_congr_if (h₁ : c₁ ≃ c₁') (h₂ : c₂ ≃ c₂') :
  ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃ ⟨{ if ↑b then ↑c₁' else ↑c₂' endif }⟩ := by
  -- FILL IN HERE (optional: PR will pass without it)
  sorry

set_option warn.sorry false in
theorem bequiv_congr_while (h : b ≃ b') :
  ⟨{ while ↑b do ↑c od }⟩ ≃ ⟨{ while ↑b' do ↑c od }⟩ := by
  intros σ σ'
  apply Iff.intro
  intros h1
  -- generalize hx : (σ =[while ↑b' do ↑c od]=> σ') = e
  induction (σ =[while ↑b' do ↑c od]=> σ') with
  | refl => sorry
  sorry


set_option warn.sorry false in
theorem equiv_congr_while {c c' : Com} (h : c ≃ c') :
  ⟨{ while ↑b do ↑c od }⟩ ≃ ⟨{ while ↑b do ↑c' od }⟩ := by
  -- FILL IN HERE (optional: PR will pass without it)
  sorry
