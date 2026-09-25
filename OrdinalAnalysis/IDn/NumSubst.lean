/- Source: OrdinalAnalysis\ID1\NumSubst.lean (one-level `Omega`/`Stage` generalised to level `k : Fin n`). -/

import OrdinalAnalysis.IDn.Calculus
import OrdinalAnalysis.IDn.Evaluate
/-
  The translation of `(LXIn n)` into `(LIinfN n)`, and numeral substitutions.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, §6, before Proposition 6.4 (the translation
  `ψ ↦ ψ⁺`, `I_φ ↦ I^{≺Ω}_φ`) and the proof of Theorem 6.5 (the universal quantifier case,
  after Theorem 3.7 of the first lecture).

  **The translation.**  Freund's `ψ⁺` replaces the predicate `I` by `I^{≺Ω}`; that is
  `embed`.  The language `(LXIn n)` also has the free predicate `X`, which Freund's `L_ID` does
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

set_option autoImplicit false

namespace OrdinalAnalysis
variable {n : ℕ} (k : Fin n)

namespace IDn

open LO LO.FirstOrder
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting

/-! ### Reading `X` as empty -/

section KillX

variable {ξ : Type*}

/-- An atom with `X` read as empty. -/
def killRel {m : ℕ} : {k : ℕ} → (LXIn n).Rel k → (Fin k → Semiterm (LXIn n) ξ m) → Semiformula (LXIn n) ξ m
  | _, Sum.inl r, v => .rel (Sum.inl r) v
  | _, Sum.inr IXRelN.X, _ => ⊥
  | _, Sum.inr (IXRelN.I j), v => .rel (Sum.inr (IXRelN.I j)) v

/-- A negated atom with `X` read as empty. -/
def killNrel {m : ℕ} : {k : ℕ} → (LXIn n).Rel k → (Fin k → Semiterm (LXIn n) ξ m) → Semiformula (LXIn n) ξ m
  | _, Sum.inl r, v => .nrel (Sum.inl r) v
  | _, Sum.inr IXRelN.X, _ => ⊤
  | _, Sum.inr (IXRelN.I j), v => .nrel (Sum.inr (IXRelN.I j)) v

/-- **`X` read as the empty predicate**: `X t ↦ ⊥`, `¬X t ↦ ⊤`. -/
def killX : {m : ℕ} → Semiformula (LXIn n) ξ m → Semiformula (LXIn n) ξ m
  | _, .verum => ⊤
  | _, .falsum => ⊥
  | _, .rel r v => killRel r v
  | _, .nrel r v => killNrel r v
  | _, .and φ ψ => killX φ ⋏ killX ψ
  | _, .or φ ψ => killX φ ⋎ killX ψ
  | _, .all φ => ∀¹ killX φ
  | _, .exs φ => ∃¹ killX φ

@[simp] theorem killX_verum {m : ℕ} : killX (⊤ : Semiformula (LXIn n) ξ m) = ⊤ := rfl

@[simp] theorem killX_falsum {m : ℕ} : killX (⊥ : Semiformula (LXIn n) ξ m) = ⊥ := rfl

@[simp] theorem killX_and {m : ℕ} (φ ψ : Semiformula (LXIn n) ξ m) :
    killX (φ ⋏ ψ) = killX φ ⋏ killX ψ := rfl

@[simp] theorem killX_or {m : ℕ} (φ ψ : Semiformula (LXIn n) ξ m) :
    killX (φ ⋎ ψ) = killX φ ⋎ killX ψ := rfl

@[simp] theorem killX_all {m : ℕ} (φ : Semiformula (LXIn n) ξ (m + 1)) : killX (∀¹ φ) = ∀¹ killX φ :=
  rfl

@[simp] theorem killX_exs {m : ℕ} (φ : Semiformula (LXIn n) ξ (m + 1)) : killX (∃¹ φ) = ∃¹ killX φ :=
  rfl

theorem killX_rel {m k : ℕ} (r : (LXIn n).Rel k) (v : Fin k → Semiterm (LXIn n) ξ m) :
    killX (Semiformula.rel r v) = killRel r v := rfl

theorem killX_nrel {m k : ℕ} (r : (LXIn n).Rel k) (v : Fin k → Semiterm (LXIn n) ξ m) :
    killX (Semiformula.nrel r v) = killNrel r v := rfl

theorem neg_killRel {m k : ℕ} (r : (LXIn n).Rel k) (v : Fin k → Semiterm (LXIn n) ξ m) :
    ∼(killRel r v) = killNrel r v := by
  rcases r with r | r
  · rfl
  · cases r <;> rfl

@[simp] theorem killX_neg {m : ℕ} (φ : Semiformula (LXIn n) ξ m) : killX (∼φ) = ∼(killX φ) := by
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

theorem killX_imp {m : ℕ} (φ ψ : Semiformula (LXIn n) ξ m) :
    killX (φ 🡒 ψ) = killX φ 🡒 killX ψ := by
  simp [Semiformula.imp_eq]

theorem rew_killRel {ξ₁ ξ₂ : Type*} {n₁ n₂ k : ℕ} (ω : Rew (LXIn n) ξ₁ n₁ ξ₂ n₂) (r : (LXIn n).Rel k)
    (v : Fin k → Semiterm (LXIn n) ξ₁ n₁) : ω ▹ killRel r v = killRel r (ω ∘ v) := by
  rcases r with r | r
  · exact Semiformula.rew_rel _ _ _
  · cases r
    · simp only [killRel, LogicalConnective.HomClass.map_bot]
    · exact Semiformula.rew_rel _ _ _

theorem rew_killNrel {ξ₁ ξ₂ : Type*} {n₁ n₂ k : ℕ} (ω : Rew (LXIn n) ξ₁ n₁ ξ₂ n₂) (r : (LXIn n).Rel k)
    (v : Fin k → Semiterm (LXIn n) ξ₁ n₁) : ω ▹ killNrel r v = killNrel r (ω ∘ v) := by
  rcases r with r | r
  · exact Semiformula.rew_nrel _ _ _
  · cases r
    · simp only [killNrel, LogicalConnective.HomClass.map_top]
    · exact Semiformula.rew_nrel _ _ _

/-- **Reading `X` as empty commutes with every rewriting.** -/
theorem killX_rew {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew (LXIn n) ξ₁ n₁ ξ₂ n₂)
    (φ : Semiformula (LXIn n) ξ₁ n₁) : killX (ω ▹ φ) = ω ▹ killX φ := by
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
theorem killX_eq_self {m : ℕ} : ∀ (φ : Semiformula (LXIn n) ξ m), XFreeL φ → killX φ = φ
  | .verum, _ => rfl
  | .falsum, _ => rfl
  | .rel (Sum.inl _) _, _ => rfl
  | .rel (Sum.inr IXRelN.X) _, h => h.elim
  | .rel (Sum.inr (IXRelN.I _)) _, _ => rfl
  | .nrel (Sum.inl _) _, _ => rfl
  | .nrel (Sum.inr IXRelN.X) _, h => h.elim
  | .nrel (Sum.inr (IXRelN.I _)) _, _ => rfl
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

theorem killX_allClosure : ∀ {m : ℕ} (φ : Semiformula (LXIn n) ξ m), killX (∀¹* φ) = ∀¹* killX φ
  | 0, _ => rfl
  | _ + 1, φ => killX_allClosure (∀¹ φ)

end KillX

/-! ### The embedding with `X` read as empty -/

section EmbK

variable {ξ : Type*}

/-- **The embedding** `(LXIn n) → (LIinfN n)`: `I ↦ I^{≺Ω}` (Freund's `ψ⁺`), with `X` read as empty. -/
def embK {m : ℕ} (φ : Semiformula (LXIn n) ξ m) : Semiformula (LIinfN n) ξ m := embed (killX φ)

/-- The term part of the embedding. -/
abbrev embT {m : ℕ} (t : Semiterm (LXIn n) ξ m) : Semiterm (LIinfN n) ξ m :=
  Semiterm.lMap (stageHom k (StageAt.top k.val)) t

@[simp] theorem embK_verum {m : ℕ} : embK (⊤ : Semiformula (LXIn n) ξ m) = ⊤ := by simp [embK, embed]

@[simp] theorem embK_falsum {m : ℕ} : embK (⊥ : Semiformula (LXIn n) ξ m) = ⊥ := by simp [embK, embed]

@[simp] theorem embK_and {m : ℕ} (φ ψ : Semiformula (LXIn n) ξ m) :
    embK (φ ⋏ ψ) = embK φ ⋏ embK ψ := by simp [embK, embed]

@[simp] theorem embK_or {m : ℕ} (φ ψ : Semiformula (LXIn n) ξ m) :
    embK (φ ⋎ ψ) = embK φ ⋎ embK ψ := by simp [embK, embed]

@[simp] theorem embK_all {m : ℕ} (φ : Semiformula (LXIn n) ξ (m + 1)) : embK (∀¹ φ) = ∀¹ embK φ := by
  simp [embK, embed]

@[simp] theorem embK_exs {m : ℕ} (φ : Semiformula (LXIn n) ξ (m + 1)) : embK (∃¹ φ) = ∃¹ embK φ := by
  simp [embK, embed]

@[simp] theorem embK_neg {m : ℕ} (φ : Semiformula (LXIn n) ξ m) : embK (∼φ) = ∼(embK φ) := by
  simp [embK, embed]

theorem embK_imp {m : ℕ} (φ ψ : Semiformula (LXIn n) ξ m) : embK (φ 🡒 ψ) = embK φ 🡒 embK ψ := by
  simp [Semiformula.imp_eq]

theorem embK_allClosure {m : ℕ} (φ : Semiformula (LXIn n) ξ m) : embK (∀¹* φ) = ∀¹* embK φ := by
  rw [embK, killX_allClosure, embed, Semiformula.lMap_allClosure]; rfl

/-- `I t ↦ I^{≺Ω} t`. -/
theorem embK_Iat {m : ℕ} (t : Semiterm (LXIn n) ξ m) : embK (Iat k t) = IOmegaAt k (embT k t) := by
  show embed (Iat k t) = IOmegaAt k (embT k t)
  rw [embT, stageHom_top]
  exact embed_Iat k t

/-- `X t ↦ ⊥`. -/
theorem embK_Xat {m : ℕ} (t : Semiterm (LXIn n) ξ m) : embK (Xat t) = ⊥ := by
  show embed (⊥ : Semiformula (LXIn n) ξ m) = ⊥
  simp [embed]

theorem embK_eq_embed {m : ℕ} {φ : Semiformula (LXIn n) ξ m} (h : XFreeL φ) : embK φ = embed φ := by
  rw [embK, killX_eq_self φ h]

theorem embK_subst {m l : ℕ} (w : Fin l → Semiterm (LXIn n) ξ m) (φ : Semiformula (LXIn n) ξ l) :
    embK (φ ⇜ w) = (embK φ) ⇜ (embT k ∘ w) := by
  have hw : embT k ∘ w = Semiterm.lMap embedHom ∘ w := by
    funext i; show embT k (w i) = _; rw [embT, stageHom_top]; rfl
  rw [hw, embK, embK, killX_rew, embed, embed, Semiformula.lMap_subst]

theorem embK_subst₁ (φ : Semiformula (LXIn n) ξ 1) {m : ℕ} (t : Semiterm (LXIn n) ξ m) :
    embK (φ/[t]) = (embK φ)/[embT k t] := by
  rw [show φ/[t] = φ ⇜ ![t] from rfl, embK_subst]
  congr 2
  funext i
  obtain rfl := Subsingleton.elim i 0
  rfl

theorem embK_free {m : ℕ} (φ : Semiformula (LXIn n) ℕ (m + 1)) :
    embK (Rewriting.free φ) = Rewriting.free (embK φ) := by
  rw [embK, embK, show Rewriting.free φ = @Rew.free (LXIn n) m ▹ φ from rfl, killX_rew, embed, embed,
    Semiformula.lMap_free]

theorem embK_shift {m : ℕ} (φ : Semiformula (LXIn n) ℕ m) :
    embK (Rewriting.shift φ) = Rewriting.shift (embK φ) := by
  rw [embK, embK, show Rewriting.shift φ = @Rew.shift (LXIn n) m ▹ φ from rfl, killX_rew, embed,
    embed, Semiformula.lMap_shift]

theorem embK_emb {m : ℕ} (φ : Semiformula (LXIn n) Empty m) :
    embK (Rewriting.emb φ : Semiformula (LXIn n) ℕ m) = Rewriting.emb (embK φ) := by
  rw [embK, embK, show (Rewriting.emb φ : Semiformula (LXIn n) ℕ m) = (Rew.emb ▹ φ) from rfl,
    killX_rew, embed, embed]
  exact Semiformula.lMap_emb _

theorem xFreeI_embK {m : ℕ} (φ : Semiformula (LXIn n) ξ m) : XFreeI (embK φ) := by
  induction φ using Semiformula.rec' with
  | hverum => rw [embK_verum]; trivial
  | hfalsum => rw [embK_falsum]; trivial
  | hrel r v =>
    rcases r with r | r
    · exact fun h => h
    · cases r
      · show XFreeI (embK (⊥ : Semiformula (LXIn n) ξ _))
        rw [embK_falsum]; trivial
      · exact fun h => h
  | hnrel r v =>
    rcases r with r | r
    · exact fun h => h
    · cases r
      · show XFreeI (embK (⊤ : Semiformula (LXIn n) ξ _))
        rw [embK_verum]; trivial
      · exact fun h => h
  | hand φ ψ ihφ ihψ => rw [embK_and]; exact ⟨ihφ, ihψ⟩
  | hor φ ψ ihφ ihψ => rw [embK_or]; exact ⟨ihφ, ihψ⟩
  | hall φ ih => rw [embK_all]; exact ih
  | hexs φ ih => rw [embK_exs]; exact ih

theorem params_embK {m : ℕ} (φ : Semiformula (LXIn n) ξ m) :
    params (embK φ) ⊆ {s : Stage n | ∃ j : Fin n, s = Stage.top j} :=
  params_embed (killX φ)

end EmbK

/-! ### Numeral substitutions -/

section NumSubst

/-- The substitution sending the free variable `x` to the numeral of `f x`. -/
def numSubst (f : ℕ → ℕ) : Rew (LIinfN n) ℕ 0 ℕ 0 := Rew.rewrite fun x => numI (f x)

/-- The same substitution, one binder down. -/
def numSubst₁ (f : ℕ → ℕ) : Rew (LIinfN n) ℕ 1 ℕ 1 :=
  Rew.rewrite fun x => (Semiterm.numeral (f x) : Semiterm (LIinfN n) ℕ 1)

@[simp] theorem numSubst_fvar (f : ℕ → ℕ) (x : ℕ) :
    numSubst f &x = (numI (f x) : Semiterm (LIinfN n) ℕ 0) := rfl

@[simp] theorem numSubst₁_fvar (f : ℕ → ℕ) (x : ℕ) :
    numSubst₁ f &x = (Semiterm.numeral (f x) : Semiterm (LIinfN n) ℕ 1) := rfl

@[simp] theorem numSubst₁_bvar (f : ℕ → ℕ) (x : Fin 1) :
    numSubst₁ f #x = (#x : Semiterm (LIinfN n) ℕ 1) := rfl

@[simp] theorem numSubst_q (f : ℕ → ℕ) :
    (numSubst f).q = (numSubst₁ f : Rew (LIinfN n) ℕ 1 ℕ 1) := by
  simp only [numSubst, numSubst₁]
  ext x <;> simp [numI]

/-- The pointwise action on a sequent. -/
def seqSubst (f : ℕ → ℕ) (Γ : Sequent (LIinfN n)) : Sequent (LIinfN n) := Γ.map (numSubst f ▹ ·)

theorem numSubst_all (f : ℕ → ℕ) (φ : Semiproposition (LIinfN n) 1) :
    numSubst f ▹ (∀¹ φ) = ∀¹ (numSubst₁ f ▹ φ) := by
  rw [Rewriting.app_all, numSubst_q]

theorem numSubst_exs (f : ℕ → ℕ) (φ : Semiproposition (LIinfN n) 1) :
    numSubst f ▹ (∃¹ φ) = ∃¹ (numSubst₁ f ▹ φ) := by
  rw [Rewriting.app_exs, numSubst_q]

/-- **The `all` premise**: assigning `n` to the fresh variable of `φ.free` is the `n`-th
instance of the body under `f`. -/
theorem numSubst_free (f : ℕ → ℕ) (m : ℕ) (φ : Semiproposition (LIinfN n) 1) :
    numSubst (m :>ₙ f) ▹ Rewriting.free φ = (numSubst₁ f ▹ φ)/[numI m] := by
  simp only [numSubst, numSubst₁]
  simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app, numI]

/-- **The shifted context**: under `n :>ₙ f` a shifted formula is the formula under `f`. -/
theorem numSubst_shift (f : ℕ → ℕ) (m : ℕ) (φ : Proposition (LIinfN n)) :
    numSubst (m :>ₙ f) ▹ Rewriting.shift φ = numSubst f ▹ φ := by
  simp only [numSubst]
  simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app]

theorem seqSubst_shifts (f : ℕ → ℕ) (m : ℕ) (Γ : Sequent (LIinfN n)) :
    seqSubst (m :>ₙ f) Γ⁺ = seqSubst f Γ := by
  induction Γ with
  | nil => rfl
  | cons φ Γ ih => simp [seqSubst, Rewriting.shifts_cons, numSubst_shift] at ih ⊢; exact ih

/-- **The `exs` premise**: the witness becomes the closed term `numSubst f t`. -/
theorem numSubst_subst (f : ℕ → ℕ) (t : SyntacticTerm (LIinfN n)) (φ : Semiproposition (LIinfN n) 1) :
    numSubst f ▹ (φ/[t]) = (numSubst₁ f ▹ φ)/[numSubst f t] := by
  simp only [numSubst, numSubst₁]
  simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app, numI]

/-- On a formula without free variables every numeral substitution is the identity. -/
theorem numSubst_eq_self {f : ℕ → ℕ} {φ : Proposition (LIinfN n)} (h : φ.freeVariables = ∅) :
    numSubst f ▹ φ = φ := by
  refine Semiformula.rew_eq_self_of (fun x => Fin.elim0 x) ?_
  intro x hx
  have hx' : x ∈ Semiformula.freeVariables φ := hx
  rw [h] at hx'
  exact absurd hx' (by simp)

/-- A rewriting sending every variable to a term without free variables yields a formula
without free variables. -/
theorem freeVariables_rew_closed {n₁ n₂ : ℕ} (ω : Rew (LIinfN n) ℕ n₁ ℕ n₂)
    (hb : ∀ x, (ω #x).freeVariables = ∅) (hf : ∀ x, (ω &x).freeVariables = ∅)
    (φ : Semiformula (LIinfN n) ℕ n₁) : (ω ▹ φ).freeVariables = ∅ := by
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

theorem freeVariables_numSubst (f : ℕ → ℕ) (φ : Proposition (LIinfN n)) :
    (numSubst f ▹ φ).freeVariables = ∅ :=
  freeVariables_rew_closed _ (fun x => x.elim0) (fun _ => numI_freeVariables _) φ

theorem freeVariables_numSubst₁ (f : ℕ → ℕ) (φ : Semiformula (LIinfN n) ℕ 1) :
    (numSubst₁ f ▹ φ).freeVariables = ∅ :=
  freeVariables_rew_closed _ (fun x => by rw [numSubst₁_bvar]; rfl)
    (fun x => numeral_freeVariables _) φ

theorem freeVariables_numSubst_term' (f : ℕ → ℕ) (t : SyntacticTerm (LIinfN n)) :
    (numSubst f t).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiterm.fvar?_rew (ω := numSubst f) (t := t) (x := x) hx with ⟨i, -⟩ | ⟨z, -, hz⟩
  · exact i.elim0
  · have hz' : x ∈ (numSubst f &z).freeVariables := hz
    rw [numSubst_fvar, numI_freeVariables] at hz'
    exact Finset.notMem_empty x hz'

theorem xFreeI_numSubst (f : ℕ → ℕ) {φ : Proposition (LIinfN n)} (h : XFreeI φ) :
    XFreeI (numSubst f ▹ φ) := (xFreeI_rew _ _).mpr h

theorem params_numSubst (f : ℕ → ℕ) (φ : Proposition (LIinfN n)) :
    params (numSubst f ▹ φ) = params φ := params_rew _ φ

/-- **The translation under an assignment**: `φ ↦ embK φ` with the free variable `x`
read as the numeral of `f x`. -/
def tr (f : ℕ → ℕ) (φ : Proposition (LXIn n)) : Proposition (LIinfN n) := numSubst f ▹ embK φ

theorem tr_neg (f : ℕ → ℕ) (φ : Proposition (LXIn n)) : tr f (∼φ) = ∼(tr f φ) := by
  simp [tr]

theorem freeVariables_tr (f : ℕ → ℕ) (φ : Proposition (LXIn n)) : (tr f φ).freeVariables = ∅ :=
  freeVariables_numSubst f _

theorem xFreeI_tr (f : ℕ → ℕ) (φ : Proposition (LXIn n)) : XFreeI (tr f φ) :=
  xFreeI_numSubst f (xFreeI_embK φ)

theorem params_tr (f : ℕ → ℕ) (φ : Proposition (LXIn n)) :
    params (tr f φ) ⊆ {s : Stage n | ∃ j : Fin n, s = Stage.top j} := by
  rw [tr, params_numSubst]; exact params_embK φ

/-- On a sentence the assignment is invisible. -/
theorem tr_emb (f : ℕ → ℕ) (σ : Sentence (LXIn n)) :
    tr f (Rewriting.emb σ : Proposition (LXIn n)) = Rewriting.emb (embK σ) := by
  rw [tr, embK_emb, numSubst_eq_self (Semiformula.freeVariables_emb _)]

end NumSubst

end IDn

end OrdinalAnalysis
