import CertIMP.Hoare.Logic

open AExp
open BExp

namespace Hoare

lemma hoare_skip : ⊨ ⦃ P ⦄ ⟨{ skip }⟩ ⦃ P ⦄ :=
  -- different: term-mode, pattern-match the only constructor
  fun _ _ h p => match h with | .ESkip => p

lemma hoare_asgn : ⊨ ⦃ P[a // x] ⦄ ⟨{ ↑x = ↑a }⟩ ⦃ P ⦄ := by
  -- different: `subst` the result state, then rewrite via the value equation
  intro σ σ' h p
  cases h with
  | EAsgn na σ'σ =>
      rw [Assertion.subst] at p
      subst σ'σ
      rwa [na]

lemma hoare_seq
    (h₁ : ⊨ ⦃ P ⦄ c₁ ⦃ Q ⦄)
    (h₂ : ⊨ ⦃ Q ⦄ c₂ ⦃ R ⦄) :
  ⊨ ⦃ P ⦄ ⟨{ ↑c₁ ; ↑c₂}⟩ ⦃ R ⦄ := by
  -- different: term-mode rebuild after destructuring the sequence
  intro σ σ' h p
  cases h with
  | ESeq hc1 hc2 => exact h₂ _ _ hc2 (h₁ _ _ hc1 p)

lemma hoare_if {b : BExp}
      (h₁ : ⊨ ⦃ P ∧ b ⦄ c₁ ⦃ Q ⦄)
      (h₂ : ⊨ ⦃ P ∧ ¬b ⦄ c₂ ⦃ Q ⦄) :
  ⊨ ⦃ P ⦄ ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ⦃ Q ⦄ := by
  -- different: term-mode, feed each branch's hypothesis the paired precondition
  intro σ σ' h p
  cases h with
  | EIfTrue bt hc => exact h₁ σ σ' hc ⟨p, bt⟩
  | EIfFalse bf hc => exact h₂ σ σ' hc ⟨p, by simp [bf]⟩

lemma hoare_while {b : BExp}
      (h : ⊨ ⦃ P ∧ b ⦄ c ⦃ P ⦄) :
  ⊨ ⦃ P ⦄ ⟨{ while ↑b do ↑c od }⟩ ⦃ P ∧ ¬b ⦄ := by
  generalize W : ⟨{ while ↑b do ↑c od }⟩ = loop
  intros σ σ' h' p
  induction h' with
  | EWhileFalse bf =>
    simp only [Com.CWhile.injEq] at W
    unfold Assertion.and
    unfold Assertion.neg
    simp only [Bool.not_eq_true]
    rcases W with ⟨bb', _⟩
    rw [bb']
    exact ⟨p, bf⟩
  | @EWhileTrue σ'' c' σ''' b' σ'''' bt σ''σ''' σ'''σ'''' h' h'' =>
    specialize h'' W
    apply h''
    simp only [Com.CWhile.injEq] at W
    rcases W with ⟨bb_cross, cc_cross⟩
    rw [bb_cross, cc_cross] at h
    specialize h σ'' σ''' σ''σ'''
    unfold Assertion.and at h
    exact h ⟨p, bt⟩
  | _ => aesop

lemma hoare_consequence
    (hPre : P ->> P')
    (hPost : Q' ->> Q)
    (hH : ⊨ ⦃ P' ⦄ c ⦃ Q' ⦄) :
  ⊨ ⦃ P ⦄ c ⦃ Q ⦄ := by
  -- different: term-mode composition of the three implications
  intro σ σ' h p
  exact hPost σ' (hH σ σ' h (hPre σ p))

def Soundness :
  ⊢ ⦃ P ⦄ c ⦃ Q ⦄ → ⊨ ⦃ P ⦄ c ⦃ Q ⦄ := by
  intro h
  induction h with
  | HSkip =>
      exact hoare_skip
  | HAsgn =>
      exact hoare_asgn
  | HSeq _ _ ih₁ ih₂ =>
      apply hoare_seq <;> assumption
  | HIf _ _ ih₁ ih₂ =>
      exact hoare_if ih₁ ih₂
  | @HWhile P c b _ ih =>
      exact hoare_while ih
  | HConsequence _ _ _ ih =>
      apply hoare_consequence <;> assumption

end Hoare
