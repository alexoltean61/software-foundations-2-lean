import SoftwareFoundations2.Equiv.Def

open ComEval

namespace PgmEquiv

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
    | ESeq hc hs =>
      cases hs
      exact hc
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
    | EIfFalse _ hc2 => exact hc2
  · intro h1
    apply EIfFalse _ h1
    apply h

theorem swap_if_branches :
    ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃
    ⟨{ if !↑b then ↑c₂ else ↑c₁ endif }⟩ := by
  intro σ σ'
  apply Iff.intro
  · -- if b then c1 else c2 -> if !b then c2 else c1
    intro h
    cases h with
    | EIfTrue hb hc1 =>
        apply EIfFalse
        · simp [BExp.eval] at *; assumption
        · exact hc1
    | EIfFalse hb hc2 =>
        apply EIfTrue
        · simp [BExp.eval] at *; assumption
        · exact hc2
  · -- if !b then c2 else c1 -> if b then c1 else c2
    intro h
    cases h with
    | EIfTrue hnotb hc2 =>
        apply EIfFalse
        · simp [BExp.eval] at hnotb; assumption
        · exact hc2
    | EIfFalse hnotb hc1 =>
        apply EIfTrue
        · simp [BExp.eval] at hnotb; assumption
        · exact hc1

theorem true_while
  (h : b ≃ bexp⟨{ btrue }⟩) :
  ⟨{ while ↑b do ↑c od }⟩ ≃ ⟨{ while btrue do skip od }⟩ := by
  intro σ σ'
  apply Iff.intro
  · -- If the first loop terminates, it's a contradiction
    -- (while b do c od) reaches σ' is Impossible
    intro h_reaches
    -- we use true_while_nonterm
    have h_none : ¬ σ =[ while ↑b do ↑c od ]=> σ' := true_while_nonterm h
    contradiction
  · -- (while btrue do skip od) reaches σ' is Impossible
    intro h_reaches
    -- Prove btrue is equivalent to itself
    have h_bt : bexp⟨{ btrue }⟩ ≃ bexp⟨{ btrue }⟩ := by simp [bequiv]
    have h_none : ¬ σ =[ while btrue do skip od ]=> σ' := true_while_nonterm h_bt
    contradiction

theorem assign_aequiv
  (h : aexp⟨{ x }⟩ ≃ ↑a ) :
  ⟨{ x = ↑a }⟩ ≃ ⟨{ skip }⟩ := by
  intro σ σ'
  apply Iff.intro
  · -- (x = a) -> skip
    intro h1
    cases h1
    case EAsgn n eqn eqs =>
      subst eqn
      -- Unwrap equivalance definition
      simp only [aequiv] at h
      -- Apply it to our specific starting state
      specialize h σ
      -- Rewrute the state eq: swap 'a' out for 'x'
      rw [← h] at eqs
      -- Simplify 'ev x' to 'looking up x' which triggers set_id
      simp only [AExp.eval, State.set_id] at eqs
      subst eqs
      exact ESkip
  · -- skip -> (x = a)
    intro h2
    cases h2
    apply EAsgn rfl
    --Apply exact same logic from hypothesis 1
    simp only [aequiv] at h
    specialize h σ
    rw [← h]
    simp only [AExp.eval, State.set_id]

set_option warn.sorry false in
theorem seq_assoc : ⟨{ {↑c₁ ; ↑c₂} ; ↑c₃ }⟩ ≃ ⟨{ ↑c₁ ; {↑c₂ ; ↑c₃} }⟩ := by
  intro σ σ'
  apply Iff.intro
  · -- (c1 ; c2) ; c3 -> c1 ; (c2, c3)
    intro h
    -- Unpack outer seq --> (c1; c2) and c3
    cases h with
    | ESeq h12 h3 =>
        -- Unpack inner sequence --> c1 and c2
        cases h12 with
        | ESeq h1 h2 =>
            -- Repack them from the right
            apply ESeq
            · exact h1
            · apply ESeq
              · exact h2
              · exact h3
  · -- c1 ; (c2, c3) -> (c1 ; c2) ; c3
    intro h
    cases h with
    -- Follow the same patter --> unpack and then repack from the left
    | ESeq h1 h23 =>
        cases h23 with
        | ESeq h2 h3 =>
          apply ESeq
          · apply ESeq
            · exact h1
            · exact h2
          · exact h3

@[refl]
theorem equiv_refl : c ≃ c := by
  intro σ σ'
  apply Iff.intro
  · intro h
    exact h
  · intro h
    exact h

@[trans]
theorem equiv_trans : c₁ ≃ c₂ → c₂ ≃ c₃ → c₁ ≃ c₃ := by
  intro h12 h23
  intro σ σ'
  apply Iff.intro
  · -- c1 -> c3
    intro h_c1
    -- We use h12 to turn c1 into proof of c2
    have h_c2 := (h12 σ σ').mp h_c1
    -- Use h23 to turn c2 into proof of c3
    have h_c3 := (h23 σ σ').mp h_c2
    exact h_c3
  · -- c3 -> c1
    intro h_c3
    -- We do it backwards now c3 into c2
    have h_c2 := (h23 σ σ').mpr h_c3
    -- c2 into c1
    have h_c1 := (h12 σ σ').mpr h_c2
    exact h_c1

@[symm]
theorem equiv_symm : c₁ ≃ c₂ → c₂ ≃ c₁ := by
  intro h -- bring c1 ≃ c2 into context
  intro σ σ'
  apply Iff.intro
  · -- c2 -> c1
    intro h_c2
    have h_c1 := (h σ σ').mpr h_c2
    exact h_c1
  · -- c1 -> c2
    intro h_c1
    have h_c2 := (h σ σ').mp h_c1
    exact h_c2

theorem equiv_congr_asgn {a₁ a₂ : AExp} (h : a₁ ≃ a₂) :
  ⟨{ ↑x = ↑a₁ }⟩ ≃ ⟨{ ↑x = ↑a₂ }⟩ := by
  intro σ σ'
  apply Iff.intro
  · -- x = a₁ -> x = a₂
    intro h1
    cases h1 with
    | EAsgn eqn eqs =>
        -- Unpack equivalence hypo for this specific state
        have h_eq : a₁ ≃ a₂ := h
        simp only [aequiv] at h_eq
        specialize h_eq σ
        -- Rewrite the eqn to use a₂ instead of a₁
        rw [h_eq] at eqn

        apply EAsgn
        · exact eqn -- updated evaluation proof
        · exact eqs -- untouched state update proof
  · -- x = a₂ -> x = a₁
    intro h2
    cases h2 with
    | EAsgn eqn eqs =>
        have h_eq : a₁ ≃ a₂ := h
        simp only [aequiv] at h_eq
        specialize h_eq σ
        -- Rewrite backwards to turn a₂ back into a₁
        rw [← h_eq] at eqn

        apply EAsgn
        · exact eqn
        · exact eqs

theorem equiv_congr_seqL (h : c₁ ≃ c₁') :
  ⟨{ ↑c₁; ↑c₂ }⟩ ≃ ⟨{ ↑c₁'; ↑c₂ }⟩ := by
  intro σ σ'
  apply Iff.intro
  · -- ⟨{ ↑c₁; ↑c₂ }⟩ -> ⟨{ ↑c₁'; ↑c₂ }⟩
    intro hseq
    cases hseq with
    | ESeq h_c1 h_c2 =>
        -- Construct the new sequence
        apply ESeq
        · -- Slot 1 : use h to transform c1 into c1'
          exact (h _ _).mp h_c1
        · -- c2 stays unchanged
          exact h_c2
  · -- ⟨{ ↑c₁'; ↑c₂ }⟩ -> ⟨{ ↑c₁; ↑c₂ }⟩
    intro hseq
    cases hseq with
    | ESeq h_c1' h_c2 =>
        apply ESeq
        · exact (h _ _).mpr h_c1'
        · exact h_c2

theorem equiv_congr_seqR (h : c₂ ≃ c₂') :
  ⟨{ ↑c₁; ↑c₂ }⟩ ≃ ⟨{ ↑c₁; ↑c₂' }⟩ := by
  intro σ σ'
  apply Iff.intro
  · -- ⟨{ ↑c₁; ↑c₂ }⟩ -> ⟨{ ↑c₁'; ↑c₂ }⟩
    intro hseq
    cases hseq with
    | ESeq h_c1 h_c2 =>
        -- Construct the new sequence
        apply ESeq
        · exact h_c1
        · exact (h _ _).mp h_c2
  · -- ⟨{ ↑c₁'; ↑c₂ }⟩ -> ⟨{ ↑c₁; ↑c₂ }⟩
    intro hseq
    cases hseq with
    | ESeq h_c1 h_c2' =>
        apply ESeq
        · exact h_c1
        · exact (h _ _).mpr h_c2'

theorem bequiv_congr_if (h : b ≃ b') :
  ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃ ⟨{ if ↑b' then ↑c₁ else ↑c₂ endif }⟩ := by
  intro σ σ'
  apply Iff.intro
  · -- b -> b'
    intro h1
    cases h1 with
    | EIfTrue hb hc1 =>
        have h_eq : b ≃ b' := h
        simp only [bequiv] at h_eq
        specialize h_eq σ
        -- Rewrite so hb says : BExp.eval σ b' = true
        rw [h_eq] at hb
        -- Rebuild the new statement
        apply EIfTrue
        · exact hb
        · exact hc1
    | EIfFalse hb hc2 =>
        -- prove b' is false
        have h_eq : b ≃ b' := h
        simp only [bequiv] at h_eq
        specialize h_eq σ
        -- Rewrite so hb says : BExp.eval σ b' = true
        rw [h_eq] at hb
        -- Rebuild the new statement
        apply EIfFalse
        · exact hb
        · exact hc2
  · -- b' -> b
    intro h2
    cases h2 with
    | EIfTrue hb' hc1 =>
        have h_eq : b ≃ b' := h
        simp only [bequiv] at h_eq
        specialize h_eq σ
        -- turn b' into b
        rw [← h_eq] at hb'

        apply EIfTrue
        · exact hb'
        · exact hc1
    | EIfFalse hb' hc2 =>
        have h_eq : b ≃ b' := h
        simp only [bequiv] at h_eq
        specialize h_eq σ

        rw [← h_eq] at hb'

        apply EIfFalse
        · exact hb'
        · exact hc2

theorem equiv_congr_if (h₁ : c₁ ≃ c₁') (h₂ : c₂ ≃ c₂') :
  ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃ ⟨{ if ↑b then ↑c₁' else ↑c₂' endif }⟩ := by
  intro σ σ'
  apply Iff.intro
  · -- c1 c2 -> c1' c2'
    intro h
    cases h with
    | EIfTrue hb hc1 =>
        -- Rebuild true path
        apply EIfTrue
        · exact hb
        · exact (h₁ _ _).mp hc1
    | EIfFalse hb hc2 =>
        -- Rebuild true path
        apply EIfFalse
        · exact hb
        · exact (h₂ _ _).mp hc2
  · -- c1 c2 <- c1' c2'
    intro h
    cases h with
    | EIfTrue hb hc1' =>
        -- Rebuild true path
        apply EIfTrue
        · exact hb
        · exact (h₁ _ _).mpr hc1'
    | EIfFalse hb hc2' =>
        -- Rebuild true path
        apply EIfFalse
        · exact hb
        · exact (h₂ _ _).mpr hc2'

theorem bequiv_congr_while (h : b ≃ b') :
  ⟨{ while ↑b do ↑c od }⟩ ≃ ⟨{ while ↑b' do ↑c od }⟩ := by
  intro σ σ'
  apply Iff.intro
  · -- b -> b'
    generalize eq : ⟨{ while ↑b do ↑c od }⟩ = loop
    intro h1
    induction h1 with
    | EWhileFalse hb =>
        -- Unpack to prove b0 = b and c0 = c
        injection eq with eq_b eq_c
        subst eq_b
        subst eq_c

        -- Transform hb
        have h_eq : b ≃ b' := h
        simp only [bequiv] at h_eq
        rw [h_eq] at hb

        -- Rebuild the loop
        apply EWhileFalse
        exact hb

    | EWhileTrue hb hc hloop _ ih =>
        injection eq with eq_b eq_c
        subst eq_b
        subst eq_c

        -- Trigger induction hypo (rfl proves the equation is true)
        have ih_applied := ih rfl

        -- Transform hb
        have h_eq : b ≃ b' := h
        simp only [bequiv] at h_eq
        rw [h_eq] at hb

        -- Rebuild the loop
        apply EWhileTrue
        · exact hb          -- b'
        · exact hc
        · exact ih_applied

    | _ => contradiction

  · -- Backward Direction: while b' ... → while b ...
    generalize eq : ⟨{ while ↑b' do ↑c od }⟩ = loop
    intro h2
    induction h2 with
    | EWhileFalse hb' =>
        injection eq with eq_b eq_c
        subst eq_b
        subst eq_c

        have h_eq : b ≃ b' := h
        simp only [bequiv] at h_eq
        rw [← h_eq] at hb'

        apply EWhileFalse
        exact hb'

    | EWhileTrue hb' hc hloop _ ih =>
        injection eq with eq_b eq_c
        subst eq_b
        subst eq_c

        have ih_applied := ih rfl

        have h_eq : b ≃ b' := h
        simp only [bequiv] at h_eq
        rw [← h_eq] at hb'

        apply EWhileTrue
        · exact hb'
        · exact hc
        · exact ih_applied

    | _ => contradiction

theorem equiv_congr_while {c c' : Com} (h : c ≃ c') :
  ⟨{ while ↑b do ↑c od }⟩ ≃ ⟨{ while ↑b do ↑c' od }⟩ := by
  intro σ σ'
  apply Iff.intro
  · -- c -> c'
    generalize eq : ⟨{ while ↑b do ↑c od }⟩ = loop
    intro h1
    induction h1 with
    | EWhileFalse hb =>
        injection eq with eq_b eq_c
        subst eq_b
        subst eq_c

        -- The body never ran --> just rebuild the false loop
        apply EWhileFalse
        exact hb

    | EWhileTrue hb hc hloop _ ih =>
        injection eq with eq_b eq_c
        subst eq_b
        subst eq_c

        have ih_applied := ih rfl

        apply EWhileTrue
        · exact hb
        · exact (h _ _).mp hc        -- c turns into c'
        · exact ih_applied

    | _ => contradiction

  · -- c' -> c
    generalize eq : ⟨{ while ↑b do ↑c' od }⟩ = loop
    intro h2
    induction h2 with
    | EWhileFalse hb =>
        injection eq with eq_b eq_c'
        subst eq_b
        subst eq_c'

        apply EWhileFalse
        exact hb

    | EWhileTrue hb hc' hloop _ ih =>
        injection eq with eq_b eq_c'
        subst eq_b
        subst eq_c'

        have ih_applied := ih rfl

        apply EWhileTrue
        · exact hb
        · exact (h _ _).mpr hc'
        · exact ih_applied

    | _ => contradiction

end PgmEquiv
