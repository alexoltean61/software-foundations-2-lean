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
  intro σ σ'
  apply Iff.intro
  · intro h
    cases h with
    | ESeq h1 h2 =>
        cases h2
        exact h1
  · intro h
    apply ESeq h
    exact ESkip

theorem false_if (h : b ≃ bexp⟨{ bfalse }⟩) :
  ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃ ⟨{ ↑c₂ }⟩ := by
  intro σ σ'
  apply Iff.intro
  · intro h1
    cases h1 with
    | EIfTrue habs _ =>
        simp only [bequiv, BExp.eval] at h
        specialize h σ
        rw [h] at habs
        contradiction
    | EIfFalse _ hc2 =>
        exact hc2
  · intro h2
    apply EIfFalse _ h2
    simp only [bequiv, BExp.eval] at h
    exact h σ

theorem swap_if_branches :
    ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃
    ⟨{ if !↑b then ↑c₂ else ↑c₁ endif }⟩ := by
  intro σ σ'
  apply Iff.intro
  · intro h
    cases h with
    | EIfTrue hb hc1 =>
        apply EIfFalse
        · simp [BExp.eval, hb]
        · exact hc1
    | EIfFalse hb hc2 =>
        apply EIfTrue
        · simp [BExp.eval, hb]
        · exact hc2
  · intro h
    cases h with
    | EIfTrue hnotb hc2 =>
        apply EIfFalse
        · simp? [BExp.eval] at hnotb; exact hnotb
        · exact hc2
    | EIfFalse hnotb hc1 =>
        apply EIfTrue
        · simp? [BExp.eval] at hnotb; exact hnotb
        · exact hc1

theorem true_while
  (h : b ≃ bexp⟨{ btrue }⟩) :
  ⟨{ while ↑b do ↑c od }⟩ ≃ ⟨{ while btrue do skip od }⟩ := by
  intro σ σ'
  apply Iff.intro
  · intro hw
    have habs := true_while_nonterm h hw
    contradiction
  · intro hw
    have htrue : bexp⟨{btrue}⟩ ≃ bexp⟨{btrue}⟩ := by intro _; rfl
    have habs := true_while_nonterm htrue hw
    contradiction

theorem assign_aequiv
  (h : aexp⟨{ x }⟩ ≃ ↑a ) :
  ⟨{ x = ↑a }⟩ ≃ ⟨{ skip }⟩ := by
  intro σ σ'
  apply Iff.intro
  · intro h1
    cases h1
    case EAsgn eqn eqs =>
      subst eqn
      simp only [aequiv, AExp.eval] at h
      specialize h σ
      rw [← h] at eqs
      simp only [State.set_id] at eqs
      subst eqs
      exact ESkip
  · intro h2
    cases h2
    apply EAsgn rfl
    simp only [aequiv, AExp.eval] at h
    specialize h σ
    rw [← h]
    simp only [State.set_id]

set_option warn.sorry false in
theorem seq_assoc : ⟨{ {↑c₁ ; ↑c₂} ; ↑c₃ }⟩ ≃ ⟨{ ↑c₁ ; {↑c₂ ; ↑c₃} }⟩ := by
  -- FILL IN HERE (optional: PR will pass without it)
  sorry

@[refl]
theorem equiv_refl : c ≃ c := by
  intro σ σ'
  exact Iff.rfl

@[trans]
theorem equiv_trans : c₁ ≃ c₂ → c₂ ≃ c₃ → c₁ ≃ c₃ := by
  intro h12 h23 σ σ'
  exact Iff.trans (h12 σ σ') (h23 σ σ')

@[symm]
theorem equiv_symm : c₁ ≃ c₂ → c₂ ≃ c₁ := by
  intro h σ σ'
  exact Iff.symm (h σ σ')

set_option warn.sorry false in
theorem equiv_congr_asgn {a₁ a₂ : AExp} (h : a₁ ≃ a₂) :
  ⟨{ ↑x = ↑a₁ }⟩ ≃ ⟨{ ↑x = ↑a₂ }⟩ := by
  -- FILL IN HERE (optional: PR will pass without it)
  sorry

set_option warn.sorry false in
theorem equiv_congr_seqL (h : c₁ ≃ c₁') :
  ⟨{ ↑c₁; ↑c₂ }⟩ ≃ ⟨{ ↑c₁'; ↑c₂ }⟩ := by
  -- FILL IN HERE (optional: PR will pass without it)
  sorry

set_option warn.sorry false in
theorem equiv_congr_seqR (h : c₂ ≃ c₂') :
  ⟨{ ↑c₁; ↑c₂ }⟩ ≃ ⟨{ ↑c₁; ↑c₂' }⟩ := by
  intro σ σ'
  apply Iff.intro
  · intro hseq
    cases hseq with
    | ESeq h1 h2 =>
      apply ESeq h1
      exact (h _ _).mp h2
  · intro hseq
    cases hseq with
    | ESeq h1 h2 =>
      apply ESeq h1
      exact (h _ _).mpr h2

set_option warn.sorry false in
theorem bequiv_congr_if (h : b ≃ b') :
  ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃ ⟨{ if ↑b' then ↑c₁ else ↑c₂ endif }⟩ := by
  -- FILL IN HERE (optional: PR will pass without it)
  sorry

set_option warn.sorry false in
theorem equiv_congr_if (h₁ : c₁ ≃ c₁') (h₂ : c₂ ≃ c₂') :
  ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃ ⟨{ if ↑b then ↑c₁' else ↑c₂' endif }⟩ := by
  -- FILL IN HERE (optional: PR will pass without it)
  sorry

set_option warn.sorry false in
theorem bequiv_congr_while (h : b ≃ b') :
  ⟨{ while ↑b do ↑c od }⟩ ≃ ⟨{ while ↑b' do ↑c od }⟩ := by
  -- FILL IN HERE (optional: PR will pass without it)
  sorry

set_option warn.sorry false in
theorem equiv_congr_while {c c' : Com} (h : c ≃ c') :
  ⟨{ while ↑b do ↑c od }⟩ ≃ ⟨{ while ↑b do ↑c' od }⟩ := by
  -- FILL IN HERE (optional: PR will pass without it)
  sorry
