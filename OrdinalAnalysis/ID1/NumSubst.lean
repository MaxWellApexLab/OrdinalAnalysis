/-
  The translation of `LXI` into `LIinf`, and numeral substitutions.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, §6, before Proposition 6.4 (the translation
  `ψ ↦ ψ⁺`, `I_φ ↦ I^{≺Ω}_φ`) and the proof of Theorem 6.5 (the universal quantifier case,
  after Theorem 3.7 of the first lecture).

  **The translation.**  Freund's `ψ⁺` replaces the predicate `I` by `I^{≺Ω}`; that is
  `embed`.  The language `LXI` also has the free predicate `X`, which Freund's `L_ID` does
  not have, and the identity clause `idX` of the calculus compares the arguments of
  `X`-literals syntactically, so `X`-literals with compound closed arguments cannot be
  matched by value.  The embedding therefore reads `X` as the empty predicate, as the
  standard structure `stdInf` does:

      killX φ  :=  φ with every `X t` replaced by `⊥` and every `¬X t` by `⊤`,
      embK φ   :=  embed (killX φ).

  For an `X`-free formula `embK φ = embed φ = φ⁺` (`embK_eq_embed`).  Both maps commute
  with every rewriting (`killX_rew`, and Foundation's `lMap_*` lemmas), with negation and
  with the connectives.

  **Numeral substitutions.**  The replay of a finitary derivation proves its
  statement for every numeral instance of the sequent: the free variable `x` is sent to the
  numeral of `f x`.  The replay consumes three equations, as for the ramified language:
  `numSubst_free` (the `all` premise), `seqSubst_shifts` (the shifted context),
  `numSubst_subst` (the `exs` premise).

  Contents.

    `killX`, `killX_neg`, `killX_rew`, `killX_eq_self`
    `embK`, `embK_neg`, `embK_free`, `embK_shift`, `embK_subst`, `embK_emb`, `embK_eq_embed`,
    `xFreeI_embK`, `params_embK`
    `numSubst`, `numSubst₁`, `numSubst_all`, `numSubst_exs`, `numSubst_free`,
    `numSubst_shift`, `numSubst_subst`, `numSubst_eq_self`, `freeVariables_numSubst`
    `tr`                                   `φ ↦ (embK φ)` under the assignment `f`
-/
import OrdinalAnalysis.ID1.Evaluate

set_option autoImplicit false

namespace OrdinalAnalysis

namespace InductiveDef

open LO LO.FirstOrder
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting

/-! ### Reading `X` as empty -/

section KillX

variable {ξ : Type*}

/-- An atom with `X` read as empty. -/
def killRel {n : ℕ} : {k : ℕ} → LXI.Rel k → (Fin k → Semiterm LXI ξ n) → Semiformula LXI ξ n
  | _, Sum.inl r, v => .rel (Sum.inl r) v
  | _, Sum.inr IXRel.X, _ => ⊥
  | _, Sum.inr IXRel.I, v => .rel (Sum.inr IXRel.I) v

/-- A negated atom with `X` read as empty. -/
def killNrel {n : ℕ} : {k : ℕ} → LXI.Rel k → (Fin k → Semiterm LXI ξ n) → Semiformula LXI ξ n
  | _, Sum.inl r, v => .nrel (Sum.inl r) v
  | _, Sum.inr IXRel.X, _ => ⊤
  | _, Sum.inr IXRel.I, v => .nrel (Sum.inr IXRel.I) v

/-- **`X` read as the empty predicate**: `X t ↦ ⊥`, `¬X t ↦ ⊤`. -/
def killX : {n : ℕ} → Semiformula LXI ξ n → Semiformula LXI ξ n
  | _, .verum => ⊤
  | _, .falsum => ⊥
  | _, .rel r v => killRel r v
  | _, .nrel r v => killNrel r v
  | _, .and φ ψ => killX φ ⋏ killX ψ
  | _, .or φ ψ => killX φ ⋎ killX ψ
  | _, .all φ => ∀¹ killX φ
  | _, .exs φ => ∃¹ killX φ

@[simp] theorem killX_verum {n : ℕ} : killX (⊤ : Semiformula LXI ξ n) = ⊤ := rfl

@[simp] theorem killX_falsum {n : ℕ} : killX (⊥ : Semiformula LXI ξ n) = ⊥ := rfl

@[simp] theorem killX_and {n : ℕ} (φ ψ : Semiformula LXI ξ n) :
    killX (φ ⋏ ψ) = killX φ ⋏ killX ψ := rfl

@[simp] theorem killX_or {n : ℕ} (φ ψ : Semiformula LXI ξ n) :
    killX (φ ⋎ ψ) = killX φ ⋎ killX ψ := rfl

@[simp] theorem killX_all {n : ℕ} (φ : Semiformula LXI ξ (n + 1)) : killX (∀¹ φ) = ∀¹ killX φ :=
  rfl

@[simp] theorem killX_exs {n : ℕ} (φ : Semiformula LXI ξ (n + 1)) : killX (∃¹ φ) = ∃¹ killX φ :=
  rfl

theorem killX_rel {n k : ℕ} (r : LXI.Rel k) (v : Fin k → Semiterm LXI ξ n) :
    killX (Semiformula.rel r v) = killRel r v := rfl

theorem killX_nrel {n k : ℕ} (r : LXI.Rel k) (v : Fin k → Semiterm LXI ξ n) :
    killX (Semiformula.nrel r v) = killNrel r v := rfl

theorem neg_killRel {n k : ℕ} (r : LXI.Rel k) (v : Fin k → Semiterm LXI ξ n) :
    ∼(killRel r v) = killNrel r v := by
  rcases r with r | r
  · rfl
  · cases r <;> rfl

@[simp] theorem killX_neg {n : ℕ} (φ : Semiformula LXI ξ n) : killX (∼φ) = ∼(killX φ) := by
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => exact (neg_killRel r v).symm
  | hnrel r v =>
    show killRel r v = ∼(killNrel r v)
    rw [← neg_killRel]; simp
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

theorem killX_imp {n : ℕ} (φ ψ : Semiformula LXI ξ n) :
    killX (φ 🡒 ψ) = killX φ 🡒 killX ψ := by
  simp [Semiformula.imp_eq]

theorem rew_killRel {ξ₁ ξ₂ : Type*} {n₁ n₂ k : ℕ} (ω : Rew LXI ξ₁ n₁ ξ₂ n₂) (r : LXI.Rel k)
    (v : Fin k → Semiterm LXI ξ₁ n₁) : ω ▹ killRel r v = killRel r (ω ∘ v) := by
  rcases r with r | r
  · exact Semiformula.rew_rel _ _ _
  · cases r
    · simp only [killRel, LogicalConnective.HomClass.map_bot]
    · exact Semiformula.rew_rel _ _ _

theorem rew_killNrel {ξ₁ ξ₂ : Type*} {n₁ n₂ k : ℕ} (ω : Rew LXI ξ₁ n₁ ξ₂ n₂) (r : LXI.Rel k)
    (v : Fin k → Semiterm LXI ξ₁ n₁) : ω ▹ killNrel r v = killNrel r (ω ∘ v) := by
  rcases r with r | r
  · exact Semiformula.rew_nrel _ _ _
  · cases r
    · simp only [killNrel, LogicalConnective.HomClass.map_top]
    · exact Semiformula.rew_nrel _ _ _

/-- **Reading `X` as empty commutes with every rewriting.** -/
theorem killX_rew {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LXI ξ₁ n₁ ξ₂ n₂)
    (φ : Semiformula LXI ξ₁ n₁) : killX (ω ▹ φ) = ω ▹ killX φ := by
  induction φ using Semiformula.rec' generalizing n₂ with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => rw [Semiformula.rew_rel, killX_rel, killX_rel, rew_killRel]; rfl
  | hnrel r v => rw [Semiformula.rew_nrel, killX_nrel, killX_nrel, rew_killNrel]; rfl
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

/-- `killX` is the identity on an `X`-free formula. -/
theorem killX_eq_self {n : ℕ} : ∀ (φ : Semiformula LXI ξ n), XFreeL φ → killX φ = φ
  | .verum, _ => rfl
  | .falsum, _ => rfl
  | .rel (Sum.inl _) _, _ => rfl
  | .rel (Sum.inr IXRel.X) _, h => h.elim
  | .rel (Sum.inr IXRel.I) _, _ => rfl
  | .nrel (Sum.inl _) _, _ => rfl
  | .nrel (Sum.inr IXRel.X) _, h => h.elim
  | .nrel (Sum.inr IXRel.I) _, _ => rfl
  | .and φ ψ, h => by
    show killX φ ⋏ killX ψ = φ ⋏ ψ
    rw [killX_eq_self φ h.1, killX_eq_self ψ h.2]
  | .or φ ψ, h => by
    show killX φ ⋎ killX ψ = φ ⋎ ψ
    rw [killX_eq_self φ h.1, killX_eq_self ψ h.2]
  | .all φ, h => by
    show ∀¹ killX φ = ∀¹ φ
    rw [killX_eq_self φ h]
  | .exs φ, h => by
    show ∃¹ killX φ = ∃¹ φ
    rw [killX_eq_self φ h]

theorem killX_allClosure : ∀ {n : ℕ} (φ : Semiformula LXI ξ n), killX (∀¹* φ) = ∀¹* killX φ
  | 0, _ => rfl
  | _ + 1, φ => killX_allClosure (∀¹ φ)

end KillX

/-! ### The embedding with `X` read as empty -/

section EmbK

variable {ξ : Type*}

/-- **The embedding** `LXI → LIinf`: `I ↦ I^{≺Ω}` (Freund's `ψ⁺`), with `X` read as empty. -/
def embK {n : ℕ} (φ : Semiformula LXI ξ n) : Semiformula LIinf ξ n := embed (killX φ)

/-- The term part of the embedding. -/
abbrev embT {n : ℕ} (t : Semiterm LXI ξ n) : Semiterm LIinf ξ n :=
  Semiterm.lMap (stageHom Stage.top) t

@[simp] theorem embK_verum {n : ℕ} : embK (⊤ : Semiformula LXI ξ n) = ⊤ := by simp [embK, embed]

@[simp] theorem embK_falsum {n : ℕ} : embK (⊥ : Semiformula LXI ξ n) = ⊥ := by simp [embK, embed]

@[simp] theorem embK_and {n : ℕ} (φ ψ : Semiformula LXI ξ n) :
    embK (φ ⋏ ψ) = embK φ ⋏ embK ψ := by simp [embK, embed]

@[simp] theorem embK_or {n : ℕ} (φ ψ : Semiformula LXI ξ n) :
    embK (φ ⋎ ψ) = embK φ ⋎ embK ψ := by simp [embK, embed]

@[simp] theorem embK_all {n : ℕ} (φ : Semiformula LXI ξ (n + 1)) : embK (∀¹ φ) = ∀¹ embK φ := by
  simp [embK, embed]

@[simp] theorem embK_exs {n : ℕ} (φ : Semiformula LXI ξ (n + 1)) : embK (∃¹ φ) = ∃¹ embK φ := by
  simp [embK, embed]

@[simp] theorem embK_neg {n : ℕ} (φ : Semiformula LXI ξ n) : embK (∼φ) = ∼(embK φ) := by
  simp [embK, embed]

theorem embK_imp {n : ℕ} (φ ψ : Semiformula LXI ξ n) : embK (φ 🡒 ψ) = embK φ 🡒 embK ψ := by
  simp [Semiformula.imp_eq]

theorem embK_allClosure {n : ℕ} (φ : Semiformula LXI ξ n) : embK (∀¹* φ) = ∀¹* embK φ := by
  rw [embK, killX_allClosure, embed, Semiformula.lMap_allClosure]; rfl

/-- `I t ↦ I^{≺Ω} t`. -/
theorem embK_Iat {n : ℕ} (t : Semiterm LXI ξ n) : embK (Iat t) = IOmegaAt (embT t) :=
  embed_Iat t

/-- `X t ↦ ⊥`. -/
theorem embK_Xat {n : ℕ} (t : Semiterm LXI ξ n) : embK (Xat t) = ⊥ := by
  show embed (⊥ : Semiformula LXI ξ n) = ⊥
  simp [embed]

theorem embK_eq_embed {n : ℕ} {φ : Semiformula LXI ξ n} (h : XFreeL φ) : embK φ = embed φ := by
  rw [embK, killX_eq_self φ h]

theorem embK_subst {n k : ℕ} (w : Fin k → Semiterm LXI ξ n) (φ : Semiformula LXI ξ k) :
    embK (φ ⇜ w) = (embK φ) ⇜ (embT ∘ w) := by
  rw [embK, embK, killX_rew, embed, embed, Semiformula.lMap_subst]

theorem embK_subst₁ (φ : Semiformula LXI ξ 1) {n : ℕ} (t : Semiterm LXI ξ n) :
    embK (φ/[t]) = (embK φ)/[embT t] := by
  rw [show φ/[t] = φ ⇜ ![t] from rfl, embK_subst]
  congr 2
  funext i
  obtain rfl := Subsingleton.elim i 0
  rfl

theorem embK_free {n : ℕ} (φ : Semiformula LXI ℕ (n + 1)) :
    embK (Rewriting.free φ) = Rewriting.free (embK φ) := by
  rw [embK, embK, show Rewriting.free φ = @Rew.free LXI n ▹ φ from rfl, killX_rew, embed, embed,
    Semiformula.lMap_free]

theorem embK_shift {n : ℕ} (φ : Semiformula LXI ℕ n) :
    embK (Rewriting.shift φ) = Rewriting.shift (embK φ) := by
  rw [embK, embK, show Rewriting.shift φ = @Rew.shift LXI n ▹ φ from rfl, killX_rew, embed,
    embed, Semiformula.lMap_shift]

theorem embK_emb {n : ℕ} (φ : Semiformula LXI Empty n) :
    embK (Rewriting.emb φ : Semiformula LXI ℕ n) = Rewriting.emb (embK φ) := by
  rw [embK, embK, show (Rewriting.emb φ : Semiformula LXI ℕ n) = (Rew.emb ▹ φ) from rfl,
    killX_rew, embed, embed]
  exact Semiformula.lMap_emb _

theorem xFreeI_embK {n : ℕ} (φ : Semiformula LXI ξ n) : XFreeI (embK φ) := by
  induction φ using Semiformula.rec' with
  | hverum => rw [embK_verum]; trivial
  | hfalsum => rw [embK_falsum]; trivial
  | hrel r v =>
    rcases r with r | r
    · exact fun h => h
    · cases r
      · show XFreeI (embK (⊥ : Semiformula LXI ξ _))
        rw [embK_falsum]; trivial
      · exact fun h => h
  | hnrel r v =>
    rcases r with r | r
    · exact fun h => h
    · cases r
      · show XFreeI (embK (⊤ : Semiformula LXI ξ _))
        rw [embK_verum]; trivial
      · exact fun h => h
  | hand φ ψ ihφ ihψ => rw [embK_and]; exact ⟨ihφ, ihψ⟩
  | hor φ ψ ihφ ihψ => rw [embK_or]; exact ⟨ihφ, ihψ⟩
  | hall φ ih => rw [embK_all]; exact ih
  | hexs φ ih => rw [embK_exs]; exact ih

theorem params_embK {n : ℕ} (φ : Semiformula LXI ξ n) :
    params (embK φ) ⊆ {ThetaNote.Omega} :=
  params_embed (killX φ)

end EmbK

/-! ### Numeral substitutions -/

section NumSubst

/-- The substitution sending the free variable `x` to the numeral of `f x`. -/
def numSubst (f : ℕ → ℕ) : Rew LIinf ℕ 0 ℕ 0 := Rew.rewrite fun x => numI (f x)

/-- The same substitution, one binder down. -/
def numSubst₁ (f : ℕ → ℕ) : Rew LIinf ℕ 1 ℕ 1 :=
  Rew.rewrite fun x => (Semiterm.numeral (f x) : Semiterm LIinf ℕ 1)

@[simp] theorem numSubst_fvar (f : ℕ → ℕ) (x : ℕ) : numSubst f &x = numI (f x) := rfl

@[simp] theorem numSubst₁_fvar (f : ℕ → ℕ) (x : ℕ) :
    numSubst₁ f &x = (Semiterm.numeral (f x) : Semiterm LIinf ℕ 1) := rfl

@[simp] theorem numSubst₁_bvar (f : ℕ → ℕ) (x : Fin 1) : numSubst₁ f #x = #x := rfl

@[simp] theorem numSubst_q (f : ℕ → ℕ) : (numSubst f).q = numSubst₁ f := by
  simp only [numSubst, numSubst₁]
  ext x <;> simp [numI]

/-- The pointwise action on a sequent. -/
def seqSubst (f : ℕ → ℕ) (Γ : Sequent LIinf) : Sequent LIinf := Γ.map (numSubst f ▹ ·)

theorem numSubst_all (f : ℕ → ℕ) (φ : Semiproposition LIinf 1) :
    numSubst f ▹ (∀¹ φ) = ∀¹ (numSubst₁ f ▹ φ) := by
  rw [Rewriting.app_all, numSubst_q]

theorem numSubst_exs (f : ℕ → ℕ) (φ : Semiproposition LIinf 1) :
    numSubst f ▹ (∃¹ φ) = ∃¹ (numSubst₁ f ▹ φ) := by
  rw [Rewriting.app_exs, numSubst_q]

/-- **The `all` premise**: assigning `n` to the fresh variable of `φ.free` is the `n`-th
instance of the body under `f`. -/
theorem numSubst_free (f : ℕ → ℕ) (n : ℕ) (φ : Semiproposition LIinf 1) :
    numSubst (n :>ₙ f) ▹ Rewriting.free φ = (numSubst₁ f ▹ φ)/[numI n] := by
  simp only [numSubst, numSubst₁]
  simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app, numI]

/-- **The shifted context**: under `n :>ₙ f` a shifted formula is the formula under `f`. -/
theorem numSubst_shift (f : ℕ → ℕ) (n : ℕ) (φ : Proposition LIinf) :
    numSubst (n :>ₙ f) ▹ Rewriting.shift φ = numSubst f ▹ φ := by
  simp only [numSubst]
  simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app]

theorem seqSubst_shifts (f : ℕ → ℕ) (n : ℕ) (Γ : Sequent LIinf) :
    seqSubst (n :>ₙ f) Γ⁺ = seqSubst f Γ := by
  induction Γ with
  | nil => rfl
  | cons φ Γ ih => simp [seqSubst, Rewriting.shifts_cons, numSubst_shift] at ih ⊢; exact ih

/-- **The `exs` premise**: the witness becomes the closed term `numSubst f t`. -/
theorem numSubst_subst (f : ℕ → ℕ) (t : SyntacticTerm LIinf) (φ : Semiproposition LIinf 1) :
    numSubst f ▹ (φ/[t]) = (numSubst₁ f ▹ φ)/[numSubst f t] := by
  simp only [numSubst, numSubst₁]
  simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app, numI]

/-- On a formula without free variables every numeral substitution is the identity. -/
theorem numSubst_eq_self {f : ℕ → ℕ} {φ : Proposition LIinf} (h : φ.freeVariables = ∅) :
    numSubst f ▹ φ = φ := by
  refine Semiformula.rew_eq_self_of (fun x => Fin.elim0 x) ?_
  intro x hx
  have hx' : x ∈ Semiformula.freeVariables φ := hx
  rw [h] at hx'
  exact absurd hx' (by simp)

/-- A rewriting sending every variable to a term without free variables yields a formula
without free variables. -/
theorem freeVariables_rew_closed {n₁ n₂ : ℕ} (ω : Rew LIinf ℕ n₁ ℕ n₂)
    (hb : ∀ x, (ω #x).freeVariables = ∅) (hf : ∀ x, (ω &x).freeVariables = ∅)
    (φ : Semiformula LIinf ℕ n₁) : (ω ▹ φ).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := ω) (φ := φ) (x := x) hx with ⟨i, hi⟩ | ⟨z, -, hz⟩
  · have hi' : x ∈ (ω #i).freeVariables := hi
    rw [hb i] at hi'
    exact Finset.notMem_empty x hi'
  · have hz' : x ∈ (ω &z).freeVariables := hz
    rw [hf z] at hz'
    exact Finset.notMem_empty x hz'

theorem freeVariables_numSubst (f : ℕ → ℕ) (φ : Proposition LIinf) :
    (numSubst f ▹ φ).freeVariables = ∅ :=
  freeVariables_rew_closed _ (fun x => x.elim0) (fun _ => numI_freeVariables _) φ

theorem freeVariables_numSubst₁ (f : ℕ → ℕ) (φ : Semiformula LIinf ℕ 1) :
    (numSubst₁ f ▹ φ).freeVariables = ∅ :=
  freeVariables_rew_closed _ (fun x => by rw [numSubst₁_bvar]; rfl)
    (fun x => numeral_freeVariables _) φ

theorem freeVariables_numSubst_term' (f : ℕ → ℕ) (t : SyntacticTerm LIinf) :
    (numSubst f t).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiterm.fvar?_rew (ω := numSubst f) (t := t) (x := x) hx with ⟨i, -⟩ | ⟨z, -, hz⟩
  · exact i.elim0
  · have hz' : x ∈ (numSubst f &z).freeVariables := hz
    rw [numSubst_fvar, numI_freeVariables] at hz'
    exact Finset.notMem_empty x hz'

theorem xFreeI_numSubst (f : ℕ → ℕ) {φ : Proposition LIinf} (h : XFreeI φ) :
    XFreeI (numSubst f ▹ φ) := (xFreeI_rew _ _).mpr h

theorem params_numSubst (f : ℕ → ℕ) (φ : Proposition LIinf) :
    params (numSubst f ▹ φ) = params φ := params_rew _ φ

/-- **The translation under an assignment**: `φ ↦ embK φ` with the free variable `x`
read as the numeral of `f x`. -/
def tr (f : ℕ → ℕ) (φ : Proposition LXI) : Proposition LIinf := numSubst f ▹ embK φ

theorem tr_neg (f : ℕ → ℕ) (φ : Proposition LXI) : tr f (∼φ) = ∼(tr f φ) := by
  simp [tr]

theorem freeVariables_tr (f : ℕ → ℕ) (φ : Proposition LXI) : (tr f φ).freeVariables = ∅ :=
  freeVariables_numSubst f _

theorem xFreeI_tr (f : ℕ → ℕ) (φ : Proposition LXI) : XFreeI (tr f φ) :=
  xFreeI_numSubst f (xFreeI_embK φ)

theorem params_tr (f : ℕ → ℕ) (φ : Proposition LXI) : params (tr f φ) ⊆ {ThetaNote.Omega} := by
  rw [tr, params_numSubst]; exact params_embK φ

/-- On a sentence the assignment is invisible. -/
theorem tr_emb (f : ℕ → ℕ) (σ : Sentence LXI) :
    tr f (Rewriting.emb σ : Proposition LXI) = Rewriting.emb (embK σ) := by
  rw [tr, embK_emb, numSubst_eq_self (Semiformula.freeVariables_emb _)]

end NumSubst

end InductiveDef

end OrdinalAnalysis
