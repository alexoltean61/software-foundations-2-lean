
import CertIMP.Equiv.Def

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
  -- Hint: You'll want to use `true_while_nonterm` here.
  -- different structure: term-mode `⟨·,·⟩` for the Iff, `.elim` instead of `contradiction`
  intro σ σ'
  exact ⟨fun h1 => (true_while_nonterm h h1).elim,
         fun h2 => (true_while_nonterm (fun _ => rfl) h2).elim⟩

theorem assign_aequiv
  (h : aexp⟨{ x }⟩ ≃ ↑a ) :
  ⟨{ x = ↑a }⟩ ≃ ⟨{ skip }⟩ := by
  -- a different structure: `constructor`, an explicit `have`, and `State.set_id` directly
  intro σ σ'
  constructor
  · intro hxa
    cases hxa with
    | EAsgn heval hset =>
      have hσ : σ' = σ := by
        rw [hset, heval, show a.eval σ = σ "x" from (h σ).symm]
        exact State.set_id
      rw [hσ]
      exact ESkip
  · intro hskip
    cases hskip
    apply EAsgn (h σ)
    exact State.set_id.symm

theorem seq_assoc : ⟨{ {↑c₁ ; ↑c₂} ; ↑c₃ }⟩ ≃ ⟨{ ↑c₁ ; {↑c₂ ; ↑c₃} }⟩ := by
  -- different structure: `constructor`, then rebuild with term-mode `ESeq`
  intro σ σ'
  constructor
  · intro h
    cases h with
    | ESeq h12 h3 =>
      cases h12 with
      | ESeq h1 h2 => exact ESeq h1 (ESeq h2 h3)
  · intro h
    cases h with
    | ESeq h1 h23 =>
      cases h23 with
      | ESeq h2 h3 => exact ESeq (ESeq h1 h2) h3

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

theorem equiv_congr_asgn {a₁ a₂ : AExp} (h : a₁ ≃ a₂) :
  ⟨{ ↑x = ↑a₁ }⟩ ≃ ⟨{ ↑x = ↑a₂ }⟩ := by
  -- different structure: term-mode rebuild via `EAsgn`, chaining the value equality with `.trans`
  intro σ σ'
  constructor
  · intro h1
    cases h1 with
    | EAsgn hn hs => exact EAsgn (hn.trans (h σ)) hs
  · intro h1
    cases h1 with
    | EAsgn hn hs => exact EAsgn (hn.trans (h σ).symm) hs

theorem equiv_congr_seqL (h : c₁ ≃ c₁') :
  ⟨{ ↑c₁; ↑c₂ }⟩ ≃ ⟨{ ↑c₁'; ↑c₂ }⟩ := by
  -- different structure: term-mode rebuild, converting the first command via the iff `h`
  intro σ σ'
  constructor
  · intro hh
    cases hh with
    | ESeq hc1 hc2 => exact ESeq ((h _ _).mp hc1) hc2
  · intro hh
    cases hh with
    | ESeq hc1 hc2 => exact ESeq ((h _ _).mpr hc1) hc2

theorem equiv_congr_seqR (h : c₂ ≃ c₂') :
  ⟨{ ↑c₁; ↑c₂ }⟩ ≃ ⟨{ ↑c₁; ↑c₂' }⟩ := by
  intros σ σ'
  apply Iff.intro
  · intro h1
    cases h1 with
    | ESeq h1 h2 =>
      apply ESeq
      · exact h1
      · rw [← h]
        exact h2
  · intro h1
    cases h1 with
    | ESeq h1 h2 =>
      apply ESeq
      · exact h1
      · rw [h]
        exact h2

theorem bequiv_congr_if (h : b ≃ b') :
  ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃ ⟨{ if ↑b' then ↑c₁ else ↑c₂ endif }⟩ := by
  -- different structure: term-mode rebuild, chaining the guard equality with `.trans`
  intro σ σ'
  constructor
  · intro hh
    cases hh with
    | EIfTrue hb hc => exact EIfTrue ((h σ).symm.trans hb) hc
    | EIfFalse hb hc => exact EIfFalse ((h σ).symm.trans hb) hc
  · intro hh
    cases hh with
    | EIfTrue hb hc => exact EIfTrue ((h σ).trans hb) hc
    | EIfFalse hb hc => exact EIfFalse ((h σ).trans hb) hc

theorem equiv_congr_if (h₁ : c₁ ≃ c₁') (h₂ : c₂ ≃ c₂') :
  ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃ ⟨{ if ↑b then ↑c₁' else ↑c₂' endif }⟩ := by
  -- different structure: term-mode rebuild, converting each branch via its iff
  intro σ σ'
  constructor
  · intro hh
    cases hh with
    | EIfTrue hb hc => exact EIfTrue hb ((h₁ _ _).mp hc)
    | EIfFalse hb hc => exact EIfFalse hb ((h₂ _ _).mp hc)
  · intro hh
    cases hh with
    | EIfTrue hb hc => exact EIfTrue hb ((h₁ _ _).mpr hc)
    | EIfFalse hb hc => exact EIfFalse hb ((h₂ _ _).mpr hc)

theorem bequiv_congr_while (h : b ≃ b') :
  ⟨{ while ↑b do ↑c od }⟩ ≃ ⟨{ while ↑b' do ↑c od }⟩ := by
  -- different structure: `constructor` + term-mode `EWhile*` rebuilds
  intro σ σ'
  constructor
  · generalize eq : ⟨{ while ↑b do ↑c od }⟩ = loop
    intro h1
    induction h1 with
    | EWhileTrue htrue h1 h2 h3 h4 =>
      have h5 := h4 eq
      simp_all only [bequiv, imp_self, Com.CWhile.injEq]
      obtain ⟨left, right⟩ := eq
      subst left right
      exact EWhileTrue htrue h1 h5
    | EWhileFalse hfalse =>
      simp_all only [bequiv, Com.CWhile.injEq]
      obtain ⟨left, right⟩ := eq
      subst left right
      exact EWhileFalse hfalse
    | _ => aesop
  · generalize eq : ⟨{ while ↑b' do ↑c od }⟩ = loop
    intro h1
    induction h1 with
    | EWhileTrue htrue h1 h2 h3 h4 =>
      have h5 := h4 eq
      simp_all only [imp_self, Com.CWhile.injEq]
      obtain ⟨left, right⟩ := eq
      subst left right
      rw [← h] at htrue
      exact EWhileTrue htrue h1 h5
    | EWhileFalse hfalse =>
      simp_all only [Com.CWhile.injEq]
      obtain ⟨left, right⟩ := eq
      subst left right
      rw [← h] at hfalse
      exact EWhileFalse hfalse
    | _ => aesop

theorem equiv_congr_while {c c' : Com} (h : c ≃ c') :
  ⟨{ while ↑b do ↑c od }⟩ ≃ ⟨{ while ↑b do ↑c' od }⟩ := by
  -- different structure: `constructor` + term-mode `EWhile*` rebuilds
  intro σ σ'
  constructor
  · generalize eq : ⟨{ while ↑b do ↑c od }⟩ = loop
    intro h1
    induction h1 with
    | EWhileTrue htrue h1 h2 h3 h4 =>
      have h5 := h4 eq
      simp_all only [cequiv, imp_self, Com.CWhile.injEq]
      obtain ⟨left, right⟩ := eq
      subst left right
      exact EWhileTrue htrue h1 h5
    | EWhileFalse hfalse =>
      simp_all only [cequiv, Com.CWhile.injEq]
      obtain ⟨left, right⟩ := eq
      subst left right
      exact EWhileFalse hfalse
    | _ => aesop
  · generalize eq : ⟨{ while ↑b do ↑c' od }⟩ = loop
    intro h1
    induction h1 with
    | EWhileTrue htrue h1 h2 h3 h4 =>
      have h5 := h4 eq
      simp_all only [imp_self, Com.CWhile.injEq]
      obtain ⟨left, right⟩ := eq
      subst left right
      rw [← h] at h1
      exact EWhileTrue htrue h1 h5
    | EWhileFalse hfalse =>
      simp_all only [Com.CWhile.injEq]
      obtain ⟨left, right⟩ := eq
      subst left right
      exact EWhileFalse hfalse
    | _ => aesop

end PgmEquiv
