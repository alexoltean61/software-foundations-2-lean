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
    intros p q
    apply Iff.intro
    · intros h
      cases h with
      | ESeq h1 h2 =>
        cases h2
        exact h1
    · intro h
      apply ESeq h
      apply ESkip

theorem false_if (h : b ≃ bexp⟨{ bfalse }⟩) :
  ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃ ⟨{ ↑c₂ }⟩ := by
  -- FILL IN HERE
  intros p q
  apply Iff.intro
  · intro h1
    cases h1 with
    | EIfFalse _ _ => assumption
    | EIfTrue habs _ =>
        simp only [bequiv, BExp.eval] at h
        specialize h p
        rw [h] at habs
        contradiction
  · intro h1
    apply EIfFalse _ h1
    apply h

theorem swap_if_branches :
    ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃
    ⟨{ if !↑b then ↑c₂ else ↑c₁ endif }⟩ := by
  -- FILL IN HERE
  intros p q
  apply Iff.intro
  · intro h1
    cases h1 with
    | EIfTrue hb hthen =>
        apply EIfFalse
        · simp [hb]
        · exact hthen
    | EIfFalse hb helse =>
        apply EIfTrue
        · simp [hb]
        · exact helse
  · intro h2
    cases h2 with
    | EIfTrue hb hthen =>
        apply EIfFalse
        · simp [BExp.eval] at hb
          simp [hb]
        · exact hthen
    | EIfFalse hb helse =>
        apply EIfTrue
        · simp [BExp.eval] at hb
          simp [hb]
        · exact helse

theorem true_while
  (h : b ≃ bexp⟨{ btrue }⟩) :
  ⟨{ while ↑b do ↑c od }⟩ ≃ ⟨{ while btrue do skip od }⟩ := by
  -- FILL IN HERE
  -- Hint: You'll want to use `true_while_nonterm` here.
  intros p q
  apply Iff.intro
  · intro h1
    have hfalse := true_while_nonterm h h1
    contradiction
  · intro h1
    have hfalse := true_while_nonterm (by
      intro s
      simp [BExp.eval]
    ) h1
    contradiction

theorem assign_aequiv
  (h : aexp⟨{ x }⟩ ≃ ↑a ) :
  ⟨{ x = ↑a }⟩ ≃ ⟨{ skip }⟩ := by
  -- FILL IN HERE
  intro p q
  apply Iff.intro
  · intro h1
    cases h1 with
    | EAsgn φ ψ =>
       rw [← h] at φ
       simp at φ
       rw [ψ]
       rw [φ]
       rw [State.set_id]
       apply ESkip
    | _ => rfl
  · intro h1
    cases h1 with
    | ESkip =>
      apply EAsgn
      rw [← h p]
      simp
      rw [State.set_id]

set_option warn.sorry false in
theorem seq_assoc : ⟨{ {↑c₁ ; ↑c₂} ; ↑c₃ }⟩ ≃ ⟨{ ↑c₁ ; {↑c₂ ; ↑c₃} }⟩ := by
  -- FILL IN HERE (optional: PR will pass without it)
  intro φ ψ
  apply Iff.intro
  · intro q
    cases q with
    | ESeq q1 q2 =>
        cases q1 with
        | ESeq q1' q1'' =>
            apply ESeq q1'
            apply ESeq q1''
            exact q2
  · intro q
    cases q with
    | ESeq q1 q2 =>
      cases q2 with
      | ESeq q2' q2'' =>
        apply ESeq
        apply ESeq
        apply q1
        apply q2'
        exact q2''


@[refl]
theorem equiv_refl : c ≃ c := by
  -- FILL IN HERE
  intro φ ψ
  apply Iff.intro
  · intro q
    assumption
  · intro q
    assumption

@[trans]
theorem equiv_trans : c₁ ≃ c₂ → c₂ ≃ c₃ → c₁ ≃ c₃ := by
  -- FILL IN HERE
  intro p q φ ψ
  apply Iff.intro
  · intro h1
    rw [p] at h1
    rw [q] at h1
    assumption
  · intro h1
    rw [← q] at h1
    rw [← p] at h1
    assumption

@[symm]
theorem equiv_symm : c₁ ≃ c₂ → c₂ ≃ c₁ := by
  -- FILL IN HERE
  intro p φ ψ
  apply Iff.intro
  · intro h1
    rw [← p] at h1
    assumption
  · intro h1
    rw[ p] at h1
    assumption

set_option warn.sorry false in
theorem equiv_congr_asgn {a₁ a₂ : AExp} (h : a₁ ≃ a₂) :
  ⟨{ ↑x = ↑a₁ }⟩ ≃ ⟨{ ↑x = ↑a₂ }⟩ := by
  -- FILL IN HERE (optional: PR will pass without it)
  intro  φ ψ
  apply Iff.intro
  · intro h1
    cases h1 with
    | EAsgn h_eq h_eval =>
      apply EAsgn
      · exact h φ
      · rw [h_eq] at h_eval
        exact h_eval
  · intro h1
    cases h1 with
    | EAsgn h_eq h_eval =>
      apply EAsgn
      · rw [h φ]
      · rw [h_eq] at h_eval
        exact h_eval

set_option warn.sorry false in
theorem equiv_congr_seqL (h : c₁ ≃ c₁') :
  ⟨{ ↑c₁; ↑c₂ }⟩ ≃ ⟨{ ↑c₁'; ↑c₂ }⟩ := by
  -- FILL IN HERE (optional: PR will pass without it)
   intro  φ ψ
   apply Iff.intro
   · intro h1
     cases h1 with
     | ESeq p q =>
      apply ESeq
      · rw[← h]
        exact p
      · exact q
   · intro h1
     cases h1 with
    | ESeq p q =>
      apply ESeq
      · rw [h]
        exact p
      · exact q

set_option warn.sorry false in
theorem equiv_congr_seqR (h : c₂ ≃ c₂') :
  ⟨{ ↑c₁; ↑c₂ }⟩ ≃ ⟨{ ↑c₁; ↑c₂' }⟩ := by
  intro  φ ψ
  apply Iff.intro
  · intro h1
    cases h1 with
    | ESeq p q =>
    apply ESeq
    · exact p
    · rw[← h]
      exact q
  · intro h1
    cases h1 with
  | ESeq p q =>
    apply ESeq
    · exact p
    · rw [h]
      exact q

set_option warn.sorry false in
theorem bequiv_congr_if (h : b ≃ b') :
  ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃ ⟨{ if ↑b' then ↑c₁ else ↑c₂ endif }⟩ := by
  -- FILL IN HERE (optional: PR will pass without it)
  intro  φ ψ
  apply Iff.intro
  · intro h1
    cases h1 with
    | EIfTrue hb hthen =>
    apply EIfTrue
    · rw [← h φ]
      exact hb
    · exact hthen
    | EIfFalse hb hthen =>
    apply EIfFalse
    · rw [← h φ]
      exact hb
    · exact hthen
  · intro h1
    cases h1 with
    | EIfTrue hb hthen =>
    apply EIfTrue
    · rw [h φ]
      exact hb
    · exact hthen
    | EIfFalse hb hthen =>
    apply EIfFalse
    · rw [h φ]
      exact hb
    · exact hthen

set_option warn.sorry false in
theorem equiv_congr_if (h₁ : c₁ ≃ c₁') (h₂ : c₂ ≃ c₂') :
  ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃ ⟨{ if ↑b then ↑c₁' else ↑c₂' endif }⟩ := by
  -- FILL IN HERE (optional: PR will pass without it)
  intro  φ ψ
  apply Iff.intro
  · intro h
    cases h with
    | EIfTrue hb hthen =>
    apply EIfTrue
    ·  exact hb
    · rw [ h₁ φ] at hthen
      exact hthen
    | EIfFalse hb hthen =>
    apply EIfFalse
    · exact hb
    · rw [ h₂ φ] at hthen
      exact hthen
  · intro h
    cases h with
    | EIfTrue hb hthen =>
    apply EIfTrue
    · exact hb
    · rw [←  h₁ φ] at hthen
      exact hthen
    | EIfFalse hb hthen =>
    apply EIfFalse
    · exact hb
    · rw [← h₂ φ] at hthen
      exact hthen

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
