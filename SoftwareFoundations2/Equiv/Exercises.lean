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
    apply ESeq h ESkip

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
    | EIfFalse _ h2 =>
        exact h2
  · intro h1
    apply EIfFalse
    · apply h
    · exact h1

theorem swap_if_branches :
    ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃
    ⟨{ if !↑b then ↑c₂ else ↑c₁ endif }⟩ := by
  intro σ σ'
  constructor
  · intro h
    cases h with
    | EIfTrue hb hc1 =>
        apply EIfFalse
        · simpa [BExp.eval] using hb
        · exact hc1
    | EIfFalse hb hc2 =>
        apply EIfTrue
        · simpa [BExp.eval] using hb
        · exact hc2
  · intro h
    cases h with
    | EIfTrue hb hc2 =>
        apply EIfFalse
        · simpa [BExp.eval] using hb
        · exact hc2
    | EIfFalse hb hc1 =>
        apply EIfTrue
        · simpa [BExp.eval] using hb
        · exact hc1

theorem true_while
  (h : b ≃ bexp⟨{ btrue }⟩) :
  ⟨{ while ↑b do ↑c od }⟩ ≃ ⟨{ while btrue do skip od }⟩ := by
  intro σ σ'
  apply Iff.intro
  · intro h1
    have : False := true_while_nonterm h h1
    contradiction
  · intro h2
    have htrue : (bexp⟨{ btrue }⟩) ≃ bexp⟨{ btrue }⟩ := by
      intro σ; simp [BExp.eval]
    have : False := true_while_nonterm htrue h2
    contradiction

-- theorem assign_aequiv
--   (h : aexp⟨{ x }⟩ ≃ ↑a ) :
--   ⟨{ x = ↑a }⟩ ≃ ⟨{ skip }⟩ := by
--   intro σ σ'
--   constructor
--   · intro h1
--     cases h1
--     case EAsgn n eqn eqs =>
--       subst eqn
--       subst eqs
--       have : σ' = σ := by
--         rw [h σ]
--         simp [State.set_id]
--       subst this
--       exact ESkip
--   · intro h1
--     cases h1
--     apply EAsgn rfl
--     rw [h σ]
--     simp [State.set_id]

set_option warn.sorry false in
theorem seq_assoc : ⟨{ {↑c₁ ; ↑c₂} ; ↑c₃ }⟩ ≃ ⟨{ ↑c₁ ; {↑c₂ ; ↑c₃} }⟩ := by
  -- FILL IN HERE (optional: PR will pass without it)
  sorry

@[refl]
theorem equiv_refl : c ≃ c := by
  intro σ σ'
  constructor
  · intro h; exact h
  · intro h; exact h

@[trans]
theorem equiv_trans : c₁ ≃ c₂ → c₂ ≃ c₃ → c₁ ≃ c₃ := by
  intro h12 h23 σ σ'
  constructor
  · intro h1
    have h2 := (h12 σ σ').mp h1
    exact (h23 σ σ').mp h2
  · intro h3
    have h2 := (h23 σ σ').mpr h3
    exact (h12 σ σ').mpr h2

@[symm]
theorem equiv_symm : c₁ ≃ c₂ → c₂ ≃ c₁ := by
  intro h σ σ'
  constructor
  · intro h2
    exact (h σ σ').mpr h2
  · intro h1
    exact (h σ σ').mp h1

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
  sorry

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
