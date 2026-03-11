
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
    apply ESeq
    case mpr.σ' => exact σ'
    case mpr.a => exact h
    case mpr.a => apply ESkip

theorem false_if (h : b ≃ bexp⟨{ bfalse }⟩) :
  ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃ ⟨{ ↑c₂ }⟩ := by
  intro σ σ'
  apply Iff.intro
  · intro h
    cases h with
    | EIfTrue habs _ =>
        simp at h
        specialize h σ
        rw [h] at habs
        contradiction
    | EIfFalse _ habs => exact habs
  · intro p
    apply EIfFalse
    rw [h]
    rfl
    exact p

theorem swap_if_branches :
    ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃
    ⟨{ if !↑b then ↑c₂ else ↑c₁ endif }⟩ := by
  intro h p
  apply Iff.intro
  · intro q
    cases q with
    | EIfTrue x y =>
        apply EIfFalse
        simp
        exact x
        exact y
    | EIfFalse x y =>
      apply EIfTrue
      simp
      exact x
      exact y
  · intro q
    cases q with
    | EIfTrue x y =>
        apply EIfFalse
        simp at x
        exact x
        exact y
    | EIfFalse x y =>
        apply EIfTrue
        simp at x
        exact x
        exact y

theorem true_while
  (h : b ≃ bexp⟨{ btrue }⟩) :
  ⟨{ while ↑b do ↑c od }⟩ ≃ ⟨{ while btrue do skip od }⟩ := by
  intro p q
  apply Iff.intro
  · intro r
    apply EWhileTrue
    cases r with
    | EWhileFalse a =>
        rw [h] at a
        contradiction
    | EWhileTrue m _ _ =>
        rw [← h]
        exact m
    apply ESkip
    cases r with
    | EWhileFalse a =>
        rw [h] at a
        simp at a
    | EWhileTrue m _ _ =>
      apply true_while_nonterm at h
      contradiction
  · intro r
    apply true_while_nonterm at r
    exfalso
    exact r
    simp

theorem assign_aequiv
  (h : aexp⟨{ x }⟩ ≃ a ) :
  ⟨{ x = ↑a }⟩ ≃ ⟨{ skip }⟩ := by
  intro p q
  apply Iff.intro
  · intro r
    cases r with
    | EAsgn c d =>
        rw [← h] at c
        simp at c
        rw [c] at d
        rw [State.set_id] at d
        rw [d]
        apply ESkip
  · intro r
    apply EAsgn
    rw [← h]
    simp
    rw [State.set_id]
    cases r with
    | ESkip => rfl

theorem seq_assoc : ⟨{ {↑c₁ ; ↑c₂} ; ↑c₃ }⟩ ≃ ⟨{ ↑c₁ ; {↑c₂ ; ↑c₃} }⟩ := by
  intro h p
  apply Iff.intro
  · intro q
    cases q with
    | ESeq q1 q2 =>
        cases q1 with
        | ESeq q1 q1' =>
            apply ESeq q1
            apply ESeq q1'
            exact q2
  · intro q
    cases q with
    | ESeq q1 q2 =>
        cases q2 with
        | ESeq q2 q2' =>
            apply ESeq
            apply ESeq q1
            apply q2
            exact q2'

@[refl]
theorem equiv_refl : c ≃ c := by
  intro h p
  apply Iff.intro
  · intro r
    exact r
  · intro r
    exact r

@[trans]
theorem equiv_trans : c₁ ≃ c₂ → c₂ ≃ c₃ → c₁ ≃ c₃ := by
  intro h p q r
  apply Iff.intro
  · intro s
    rw [h] at s
    rw [p] at s
    exact s
  · intro s
    rw [← p] at s
    rw [← h] at s
    exact s

@[symm]
theorem equiv_symm : c₁ ≃ c₂ → c₂ ≃ c₁ := by
  intro h p q
  apply Iff.intro
  · intro r
    rw [← h] at r
    exact r
  · intro r
    rw [h] at r
    exact r

set_option warn.sorry false in
theorem equiv_congr_asgn {a₁ a₂ : AExp} (h : a₁ ≃ a₂) :
  ⟨{ ↑x = a₁ }⟩ ≃ ⟨{ ↑x = a₂ }⟩ := by
  -- FILL IN HERE (optional: PR will pass without it)
  simp
  intro p q
  apply Iff.intro
  · intro r
    cases r with
    | EAsgn q1 q2 =>

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
