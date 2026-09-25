/- Source: OrdinalAnalysis/ID1/Embed.lean (one-level `Omega`/`Stage` generalised to level
`k : Fin n`). Freund arXiv:2204.09321 Thm 6.5 per level.

  Deviations from a literal per-level transcription, forced by what is on disk today
  (as of 2026-09-24):

  * `IDn/{AxiomsLogic,AxiomsPA,AxiomsID,Evaluate}` are either not yet ported (`AxiomsLogic`,
    which does not exist under `IDn/`) or red (`AxiomsPA`, `AxiomsID`, `Evaluate` all fail to
    elaborate on sky4 today — checked with `lean_warm.py check`). None of their declarations
    are importable (a red file has no usable `.olean`), so every lemma this file's proof needs
    from those four files is instead taken as a field of **`EmbedHyps`**, a structure bundling
    exactly the facts `replay`/`ax_derivable_of_mem` invoke, stated per level where the source
    lemma was per-level (`closure_axiom`, `indAx_axiom`) and uniformly otherwise (`taut`,
    `eq_axiom`, `paMinus_axiom`, `induction_axiom`, `replaceHeadNumI`). `AxDerivable` itself
    needs no hypothesis: it is a plain definition over `IDnDerivable`.
  * This file uses `ThetaWNoteD.NiceS` (`Ordinal/ThetaW/HullSingle.lean`), the single
    level-free nice operator, not `ThetaWNoteD.Nice n` (`Ordinal/ThetaW/Hull.lean`, per-level):
    the calculus's meta-theory downstream of this file (`IDn/Collapsing/Theorem.lean`'s
    `collapse_zero_bound`, `IDn/Elimination.lean`'s `elimination_iter`,
    `IDn/PredCutAux.lean`'s `predicative_cut_elim`/`boundedness_self`) is all stated over
    `NiceS`, and `Hop k`/`Nice k` is *not* the same family as `HopS`/`NiceS` (adjudicated in
    Lean: `NiceS ⇏ Nice k`) — so an `embedding_theorem` quantifying over `Nice n` operators
    could not be instantiated at the `HopS`-shaped operators the consumers actually use. Every
    `Omega_mem j` (every `j`, not just level `n`) is available from `NiceS` exactly as from
    `Nice n` (`NiceS.Omega_mem`), so this is no loss of strength.
  * IDn's rank (`IDn/Rank.lean`) is **additive**, not `omegaMul`-wrapped: `rk_le_add_ofNat`
    bounds `rk φ ≤ T + ofNat φ.complexity` once every stage parameter of `φ` has
    `atomRkStage ≤ T`. Since every `s : Stage n` has `atomRkStage s ≤ Omega s.lvl.val ≤ Omega (n-1)`
    (`atomRkStage_mk_le_Omega` + `Omega_lt_Omega_iff` monotonicity), `rk φ ≤ Omega (n-1) + ofNat
    φ.complexity` holds for *every* `φ : Semiformula (LIinfN n) ξ m`, with no `omegaMul` and no
    hypothesis: this replaces `ID1.Embed`'s `omegaMul_rk_le` (`AxiomsPA`-red, and per Rank.lean's
    own header comment has no single-Omega per-level analogue) outright, and simplifies
    `OmegaPlus` to ordinary `+`, matching `Rank.lean`'s own convention (`ThetaWNoteD.nadd`
    unused in this file).

  Contents.

    `EmbedHyps`                          the four axiom lemmas and term replacement, as hypotheses
    `AxDerivable`, `OmegaTwo`             self-contained (no hypothesis needed)
    `hgt`, `cutCx`                        height and cut complexity of an `LK` derivation
    `tr_*`, `rk_le_Omega_add_ofNat`       the translation under an assignment, and its rank bound
    `replay`                             **the replay**
    `ax_derivable_of_mem`                 every axiom of `IDn n A`, dispatched to `EmbedHyps`
    `cut_axioms`                          cutting away the axioms
    `embedding_theorem`                  **Theorem 6.5**, per level (`Omega (n-1)` = `Ω_n` in place of `Omega`)
-/
import OrdinalAnalysis.IDn.NumSubst
import OrdinalAnalysis.IDn.ReductionAux

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting
open LO.FirstOrder.Arithmetic

variable {n : ℕ}

/-! ### `AxDerivable`, self-contained -/

section AxDerivable

variable (A : Fin n → Semisentence (LXIn n) 1)

/-- `Ω_n · 2` (Lean `Omega (n - 1)`, the top level's `Ω`), the height at which every axiom of
`IDn n A` is cut-free derivable (Freund, proof of Theorem 6.5). -/
abbrev OmegaTwo : ThetaWNoteD := ThetaWNoteD.Omega (n - 1) + ThetaWNoteD.Omega (n - 1)

theorem OmegaTwo_mem {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.NiceS H)
    (X : Set ThetaWNoteD) (m : ℕ) : OmegaTwo (n := n) + ThetaWNoteD.ofNat m ∈ H X :=
  hH.add_mem (hH.add_mem (hH.Omega_mem (n - 1)) (hH.Omega_mem (n - 1))) (hH.ofNat_mem m)

/-- **The axiom `σ` is derivable** in the form of Freund, proof of Theorem 6.5: cut-free, at
a height `Ω_n · 2 + m` independent of the nice operator. -/
def AxDerivable (σ : Sentence (LXIn n)) : Prop :=
  ∃ m : ℕ, ∀ H : Set ThetaWNoteD → Set ThetaWNoteD, ThetaWNoteD.NiceS H →
    IDnDerivable A ThetaWNoteD.zero H (OmegaTwo (n := n) + ThetaWNoteD.ofNat m)
      [(Rewriting.emb (embK σ) : Proposition (LIinfN n))]

theorem axDerivable_of_le {σ : Sentence (LXIn n)} (m : ℕ) (β : ThetaWNoteD)
    (hβ : β ≤ OmegaTwo (n := n) + ThetaWNoteD.ofNat m)
    (h : ∀ H : Set ThetaWNoteD → Set ThetaWNoteD, ThetaWNoteD.NiceS H →
      IDnDerivable A ThetaWNoteD.zero H β [(Rewriting.emb (embK σ) : Proposition (LIinfN n))]) :
    AxDerivable A σ :=
  ⟨m, fun H hH => (h H hH).mono_height hβ (OmegaTwo_mem hH _ _)⟩

end AxDerivable

/-! ### `EmbedHyps`: the axiom lemmas and term replacement, not yet available on disk -/

/-- **What `replay`/`ax_derivable_of_mem` need from the not-yet-green four ID₁ files
(`AxiomsLogic` — does not exist under `IDn/`; `AxiomsPA`, `AxiomsID`, `Evaluate` — red on
sky4 today), lifted per level. Every field is the statement of a real ID₁ theorem (see the
file header); none of the four files is imported, so none of their names are usable, and
these are taken as hypotheses rather than waited on. -/
structure EmbedHyps (A : Fin n → Semisentence (LXIn n) 1) where
  /-- **Freund, Lemma 6.1** (`IDn.AxiomsLogic.taut`): a closed formula and its negation are
  derivable together, cut-free, at height `ω` times its own rank — *not* `rk ψ` itself: that
  version of the field is refuted unconditionally by `IDn.taut_additive_impossible`
  (`IDn/TautAdditive.lean`, witness `ψ = ∀x. X(x)`: the ω-rule forces height `≥ ω`, but
  `rk (∀x. X(x)) = one`). -/
  taut : ∀ {H : Set ThetaWNoteD → Set ThetaWNoteD}, ThetaWNoteD.NiceS H →
    ∀ ψ : Proposition (LIinfN n), ψ.freeVariables = ∅ →
      IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H (Stage.val '' params ψ))
        (ThetaWNoteD.omegaMul (rk ψ)) [ψ, ∼ψ]
  /-- **The equality axioms** (`ID1.AxiomsLogic.eq_axiom`). -/
  eq_axiom : ∀ {σ : Sentence (LXIn n)}, σ ∈ 𝗘𝗤 (LXIn n) → AxDerivable A σ
  /-- **The `𝗣𝗔⁻` axioms** (`ID1.AxiomsLogic.paMinus_axiom`). -/
  paMinus_axiom : ∀ {σ : Sentence (LXIn n)}, σ ∈ Theory.lMap (toLXIN (Fin n)) 𝗣𝗔⁻ →
    AxDerivable A σ
  /-- **Every induction axiom of the whole language** (`ID1.AxiomsPA.induction_axiom`). -/
  induction_axiom : (∀ k, XFreeL (A k)) → ∀ {σ : Sentence (LXIn n)},
    σ ∈ InductionScheme (LXIn n) Set.univ → AxDerivable A σ
  /-- **The closure axiom at level `k`** (`ID1.AxiomsID.closure_axiom`). -/
  closure_axiom : ∀ (k : Fin n), (∀ j, XFreeL (A j)) → AxDerivable A (closureAxAt k (A k))
  /-- **The induction axiom of `I_k`** (`ID1.AxiomsID.indAx_axiom`). -/
  indAx_axiom : ∀ (k : Fin n), PositiveIn k (A k) → (∀ j, XFreeL (A j)) →
    ∀ F : Semiformula (LXIn n) ℕ 1, AxDerivable A (indAxAt k (A k) F)
  /-- **Term replacement at the head, specialised to a numeral witness**
  (`ID1.Evaluate.IDerivable.replace_head` composed with `ID1.Evaluate.sim_subst_numI`, the
  step Freund's proof of Proposition 6.4 uses for `∃`: a closed term `t` in the head formula's
  substitution slot may be replaced by the numeral of its value, for *some* value `v`). -/
  replaceHeadNumI : ∀ {ρ H α} {Γ : Sequent (LIinfN n)} {φ' : Semiformula (LIinfN n) ℕ 1}
    (t : SyntacticTerm (LIinfN n)), φ'.freeVariables = ∅ → t.freeVariables = ∅ → XFreeI φ' →
    (∀ j, XFreeL (A j)) → ThetaWNoteD.IsOperator H →
    IDnDerivable A ρ H α (φ'/[t] :: Γ) → ∃ v : ℕ, IDnDerivable A ρ H α (φ'/[numI v] :: Γ)

/-! ### Height and cut complexity of a finitary derivation -/

variable {A : Fin n → Semisentence (LXIn n) 1}

/-- The height of the replay of an `LK` derivation, above `Ω_n`. -/
def hgt : {Γ : Sequent (LXIn n)} → ⊢ᴸᴷ¹ Γ → ℕ
  | _, Derivation.identity _ _ => 0
  | _, Derivation.verum => 0
  | _, Derivation.cut dp dn => max (hgt dp) (hgt dn) + 1
  | _, Derivation.contraction d _ => hgt d
  | _, Derivation.or d => hgt d + 2
  | _, Derivation.and dp dq => max (hgt dp) (hgt dq) + 1
  | _, Derivation.all d => hgt d + 1
  | _, Derivation.exs d => hgt d + 1

/-- One more than the largest complexity of an embedded cut formula. -/
def cutCx : {Γ : Sequent (LXIn n)} → ⊢ᴸᴷ¹ Γ → ℕ
  | _, Derivation.identity _ _ => 0
  | _, Derivation.verum => 0
  | _, @Derivation.cut _ φ _ _ dp dn => max ((embK φ).complexity + 1) (max (cutCx dp) (cutCx dn))
  | _, Derivation.contraction d _ => cutCx d
  | _, Derivation.or d => cutCx d
  | _, Derivation.and dp dq => max (cutCx dp) (cutCx dq)
  | _, Derivation.all d => cutCx d
  | _, Derivation.exs d => cutCx d

/-! ### The translation under an assignment -/

section Tr

theorem tr_or (f : ℕ → ℕ) (φ ψ : Proposition (LXIn n)) : tr f (φ ⋎ ψ) = tr f φ ⋎ tr f ψ := by
  simp [tr]

theorem tr_and (f : ℕ → ℕ) (φ ψ : Proposition (LXIn n)) : tr f (φ ⋏ ψ) = tr f φ ⋏ tr f ψ := by
  simp [tr]

theorem tr_verum (f : ℕ → ℕ) : tr f ⊤ = (⊤ : Proposition (LIinfN n)) := by simp [tr]

theorem tr_all (f : ℕ → ℕ) (φ : Semiproposition (LXIn n) 1) :
    tr f (∀¹ φ) = ∀¹ (numSubst₁ f ▹ embK φ) := by
  rw [tr, embK_all, numSubst_all]

theorem tr_exs (f : ℕ → ℕ) (φ : Semiproposition (LXIn n) 1) :
    tr f (∃¹ φ) = ∃¹ (numSubst₁ f ▹ embK φ) := by
  rw [tr, embK_exs, numSubst_exs]

theorem tr_free (f : ℕ → ℕ) (m : ℕ) (φ : Semiproposition (LXIn n) 1) :
    tr (m :>ₙ f) (Rewriting.free φ) = (numSubst₁ f ▹ embK φ)/[numI m] := by
  rw [tr, embK_free, numSubst_free]

theorem tr_shifts (f : ℕ → ℕ) (m : ℕ) (Γ : Sequent (LXIn n)) :
    (Γ⁺).map (tr (m :>ₙ f)) = Γ.map (tr f) := by
  induction Γ with
  | nil => rfl
  | cons φ Γ ih =>
    rw [Rewriting.shifts_cons, List.map_cons, List.map_cons, ih, tr, tr, embK_shift,
      numSubst_shift]

/-- **`embK_subst`, with no explicit level.** `embT` (`IDn.NumSubst`) needs an explicit
`k : Fin n` (its value doesn't matter — `stageHom_top` erases it — but `tr`/`embK` at this
translation-under-an-assignment level have no `k` in scope, and `n` could be `0`), so the
translation of a substituted term is instead read off `embK`'s own definition (`embed ∘ killX`)
directly against `embedHom`, exactly as `embT`'s defining `stageHom_top` rewrite would give. -/
private theorem embK_subst_free {ξ : Type*} {m l : ℕ} (w : Fin l → Semiterm (LXIn n) ξ m)
    (φ : Semiformula (LXIn n) ξ l) :
    embK (φ ⇜ w) = (embK φ) ⇜ (Semiterm.lMap embedHom ∘ w) := by
  rw [embK, embK, killX_rew, embed, embed, Semiformula.lMap_subst]

private theorem embK_subst₁_free {ξ : Type*} (φ : Semiformula (LXIn n) ξ 1) {m : ℕ}
    (t : Semiterm (LXIn n) ξ m) :
    embK (φ/[t]) = (embK φ)/[Semiterm.lMap embedHom t] := by
  rw [show φ/[t] = φ ⇜ ![t] from rfl, embK_subst_free]
  congr 2
  funext i
  obtain rfl := Subsingleton.elim i 0
  rfl

theorem tr_subst (f : ℕ → ℕ) (φ : Semiproposition (LXIn n) 1) (t : SyntacticTerm (LXIn n)) :
    tr f (φ/[t]) = (numSubst₁ f ▹ embK φ)/[numSubst f (Semiterm.lMap embedHom t)] := by
  rw [tr, embK_subst₁_free, numSubst_subst]

/-- **`k(φ) ⊆ H(∅)` with the level tag erased**, for a `φ` whose stage parameters are all
"full at some level" (`Stage.top`): the analogue, at a single formula, of `IDn.paramsVal`
(`params`/`paramsVal` return `Set (Stage n)`, not `Set ThetaWNoteD`, so every comparison
against `H ∅` goes through `Stage.val ''`). -/
theorem paramsVal_of_params_sub {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.NiceS H)
    {ξ : Type*} {m : ℕ} {φ : Semiformula (LIinfN n) ξ m}
    (h : params φ ⊆ {s : Stage n | ∃ j : Fin n, s = Stage.top j}) :
    Stage.val '' params φ ⊆ H ∅ := by
  rintro x ⟨s, hs, rfl⟩
  obtain ⟨j, rfl⟩ := h hs
  rw [Stage.val_top]
  exact hH.Omega_mem j.val

theorem params_tr_sub {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.NiceS H)
    (f : ℕ → ℕ) (φ : Proposition (LXIn n)) : Stage.val '' params (tr f φ) ⊆ H ∅ :=
  paramsVal_of_params_sub hH (params_tr f φ)

theorem params_embK_sub {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.NiceS H)
    {ξ : Type*} {m : ℕ} (φ : Semiformula (LXIn n) ξ m) : Stage.val '' params (embK φ) ⊆ H ∅ :=
  paramsVal_of_params_sub hH (params_embK φ)

theorem paramsVal_map_tr {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.NiceS H)
    (f : ℕ → ℕ) (Γ : Sequent (LXIn n)) : paramsVal (Γ.map (tr f)) ⊆ H ∅ := by
  induction Γ with
  | nil => simp [paramsVal]
  | cons φ Γ ih =>
    rw [List.map_cons, paramsVal_cons]
    exact Set.union_subset (params_tr_sub hH f φ) ih

theorem paramsVal_cons_sub {H : Set ThetaWNoteD → Set ThetaWNoteD} {φ : Proposition (LIinfN n)}
    {Γ : Sequent (LIinfN n)} (h1 : Stage.val '' params φ ⊆ H ∅) (h2 : paramsVal Γ ⊆ H ∅) :
    paramsVal (φ :: Γ) ⊆ H ∅ := by
  rw [paramsVal_cons]; exact Set.union_subset h1 h2

/-- **Every stage parameter of any formula of `LIinfN n` has rank at most `Ω_n`** (Lean
`Omega (n - 1)`, the top level's `Ω`): every level `k : Fin n` has `k ≤ n - 1`, and the atom
`I_k^{<b}` has rank `OmegaBelow k + ω·b ≤ Omega k` (`atomRkStage_mk_le_Omega`, absorption).
The additive analogue of `ID1.Embed.omegaMul_rk_le`, needing no hypothesis. -/
theorem rk_le_Omega_add_ofNat {ξ : Type*} {m : ℕ} (φ : Semiformula (LIinfN n) ξ m) :
    rk φ ≤ ThetaWNoteD.Omega (n - 1) + ThetaWNoteD.ofNat φ.complexity := by
  refine rk_le_add_ofNat (fun s _ => ?_)
  rcases s with ⟨k, b⟩
  refine le_trans (atomRkStage_mk_le_Omega k b) ?_
  rcases Nat.lt_or_ge k.val (n - 1) with h | h
  · exact le_of_lt ((ThetaWTerm.Omega_lt_Omega_iff k.val (n - 1)).mpr h)
  · have hk : k.val = n - 1 := by have := k.isLt; omega
    rw [hk]

/-- The embedded formula of an atom has rank at most `Ω_n`: its complexity is `0`. -/
theorem rk_tr_atom_le (f : ℕ → ℕ) {k : ℕ} (r : (LXIn n).Rel k)
    (v : Fin k → SyntacticTerm (LXIn n)) :
    rk (tr f (Semiformula.rel r v)) ≤ ThetaWNoteD.Omega (n - 1) := by
  have hc : (tr f (Semiformula.rel r v)).complexity = 0 := by
    rw [tr, Semiformula.complexity_rew]
    rcases r with r | r
    · rfl
    · cases r <;> rfl
  have h := rk_le_Omega_add_ofNat (tr f (Semiformula.rel r v))
  rwa [hc, ThetaWNoteD.ofNat_zero, ThetaWNoteD.add_zero] at h

/-- **`ω · rk` of the embedded atom's translation is still `≤ Ω_n`**: `rk_tr_atom_le` gives
`rk (tr f atom) ≤ Ω_n`, and `Ω_n` (`Omega (n-1)`) absorbs `ω · ·` from at-or-below (a principal
is closed under `omegaMul` from below, `omegaMul_lt_prin`; at equality, `omegaMul_Omega`). Needed
because `EmbedHyps.taut`'s height is `omegaMul (rk ψ)`, not `rk ψ` (`taut_additive_impossible`
refutes the additive version). -/
theorem omegaMul_rk_tr_atom_le (f : ℕ → ℕ) {k : ℕ} (r : (LXIn n).Rel k)
    (v : Fin k → SyntacticTerm (LXIn n)) :
    ThetaWNoteD.omegaMul (rk (tr f (Semiformula.rel r v))) ≤ ThetaWNoteD.Omega (n - 1) := by
  rcases (rk_tr_atom_le f r v).lt_or_eq with h | h
  · exact (ThetaWNoteD.omegaMul_lt_prin (p := ThetaWNoteD.Omega (n - 1)) trivial h).le
  · rw [h, ThetaWNoteD.omegaMul_Omega]

theorem rk_tr_lt (f : ℕ → ℕ) (φ : Proposition (LXIn n)) {m : ℕ}
    (hm : (embK φ).complexity + 1 ≤ m) :
    rk (tr f φ) < ThetaWNoteD.Omega (n - 1) + ThetaWNoteD.ofNat m := by
  refine lt_of_le_of_lt (rk_le_Omega_add_ofNat _) (ThetaWNoteD.add_lt_add_left _
    (ThetaWNoteD.ofNat_lt_ofNat ?_))
  rw [tr, Semiformula.complexity_rew]; omega

end Tr

/-! ### The replay -/

section Replay

variable {H : Set ThetaWNoteD → Set ThetaWNoteD}

/-- `Ω_n + j` (Lean `Omega (n - 1)`, the top level's `Ω`: every embedded formula has rank
`≤ Ω_n + complexity`, `rk_le_Omega_add_ofNat`). At `n = 0` this is `Omega 0 + j`, harmless. -/
abbrev OmegaPlus (j : ℕ) : ThetaWNoteD := ThetaWNoteD.Omega (n - 1) + ThetaWNoteD.ofNat j

theorem OmegaPlus_mem (hH : ThetaWNoteD.NiceS H) (j : ℕ) : OmegaPlus (n := n) j ∈ H ∅ :=
  hH.add_mem (hH.Omega_mem (n - 1)) (hH.ofNat_mem j)

theorem OmegaPlus_lt {j k : ℕ} (h : j < k) : OmegaPlus (n := n) j < OmegaPlus (n := n) k :=
  ThetaWNoteD.add_lt_add_left _ (ThetaWNoteD.ofNat_lt_ofNat h)

theorem OmegaPlus_le {j k : ℕ} (h : j ≤ k) : OmegaPlus (n := n) j ≤ OmegaPlus (n := n) k :=
  ThetaWNoteD.add_le_add_left _ (ThetaWNoteD.ofNat_le_ofNat h)

theorem one_lt_OmegaPlus (j : ℕ) : ThetaWNoteD.one < OmegaPlus (n := n) j :=
  lt_of_lt_of_le (ThetaWNoteD.one_lt_prin (p := ThetaWNoteD.Omega (n - 1)) trivial)
    (ThetaWNoteD.le_self_add_red _ _)

theorem ofNat_lt_OmegaPlus (m j : ℕ) : ThetaWNoteD.ofNat m < OmegaPlus (n := n) j :=
  lt_of_lt_of_le (ThetaWNoteD.ofNat_lt_prin (p := ThetaWNoteD.Omega (n - 1)) trivial m)
    (ThetaWNoteD.le_self_add_red _ _)

theorem subset_cons_cons {α : Type*} {a : α} {Γ Δ : List α} (h : Γ ⊆ Δ) : a :: Γ ⊆ a :: Δ :=
  List.cons_subset_cons a h

/-- **The replay** (Freund, proof of Theorem 6.5): an `LK` derivation of `Γ` gives, for every
assignment `f` of numerals to the free variables, a derivation of the embedded sequent at
height `Ω_n + h` and cut rank `Ω_n + m`, with `h`, `m` read off the derivation. -/
theorem replay (hyps : EmbedHyps A) (hX : ∀ k, XFreeL (A k)) (hH : ThetaWNoteD.NiceS H) :
    ∀ {Γ : Sequent (LXIn n)} (d : ⊢ᴸᴷ¹ Γ) (f : ℕ → ℕ),
      IDnDerivable A (OmegaPlus (n := n) (cutCx d)) H (OmegaPlus (n := n) (hgt d)) (Γ.map (tr f))
  | _, Derivation.identity r v, f => by
    have hc : (tr f (Semiformula.rel r v)).freeVariables = ∅ := freeVariables_tr f _
    have d := hyps.taut hH (tr f (Semiformula.rel r v)) hc
    rw [ThetaWNoteD.adjoin_eq_self hH.1 (params_tr_sub hH f _)] at d
    have e : [Semiformula.rel r v, Semiformula.nrel r v].map (tr f) =
        [tr f (Semiformula.rel r v), ∼(tr f (Semiformula.rel r v))] := by
      rw [List.map_cons, List.map_cons, List.map_nil, ← tr_neg, Semiformula.neg_rel]
    rw [e]
    refine (d.mono_rank (ThetaWNoteD.zero_le' _)).mono_height ?_ (OmegaPlus_mem hH _)
    show ThetaWNoteD.omegaMul (rk (tr f (Semiformula.rel r v))) ≤
      ThetaWNoteD.Omega (n - 1) + ThetaWNoteD.ofNat 0
    rw [ThetaWNoteD.ofNat_zero, ThetaWNoteD.add_zero]
    exact omegaMul_rk_tr_atom_le f r v
  | _, Derivation.verum, f => by
    rw [List.map_cons, List.map_nil, tr_verum]
    exact .verum (OmegaPlus_mem hH _) (paramsVal_cons_sub (by simp) (by simp))
      List.mem_cons_self
  | _, Derivation.contraction d ss, f =>
    (replay hyps hX hH d f).weaken_seq hH.1 (List.map_subset _ ss)
      (paramsVal_map_tr hH f _)
  | _, @Derivation.or _ φ ψ Γ d, f => by
    have ih := replay hyps hX hH d f
    rw [List.map_cons, List.map_cons] at ih
    have pD : Stage.val '' params (tr f φ ⋎ tr f ψ) ⊆ H ∅ := by
      rw [← tr_or]; exact params_tr_sub hH f _
    rw [List.map_cons, tr_or]
    set D := tr f φ ⋎ tr f ψ
    have pR := paramsVal_map_tr hH f Γ
    have e1 : IDnDerivable A (OmegaPlus (n := n) (cutCx d)) H (OmegaPlus (n := n) (hgt d + 1))
        (tr f φ :: D :: Γ.map (tr f)) :=
      .orR (OmegaPlus_mem hH _) (paramsVal_cons_sub (params_tr_sub hH f φ)
          (paramsVal_cons_sub pD pR)) (List.mem_cons_of_mem _ List.mem_cons_self)
        (one_lt_OmegaPlus _) (OmegaPlus_lt (Nat.lt_succ_self _))
        (ih.weaken_seq hH.1 (by
          intro x hx; simp only [List.mem_cons] at hx ⊢; tauto)
          (paramsVal_cons_sub (params_tr_sub hH f ψ) (paramsVal_cons_sub
            (params_tr_sub hH f φ) (paramsVal_cons_sub pD pR))))
    exact .orL (OmegaPlus_mem hH _) (paramsVal_cons_sub pD pR) List.mem_cons_self
      (OmegaPlus_lt (show hgt d + 1 < hgt d + 2 by omega)) e1
  | _, @Derivation.and _ φ Γ ψ dp dq, f => by
    have ihp := replay hyps hX hH dp f
    have ihq := replay hyps hX hH dq f
    rw [List.map_cons] at ihp ihq
    have pD : Stage.val '' params (tr f φ ⋏ tr f ψ) ⊆ H ∅ := by
      rw [← tr_and]; exact params_tr_sub hH f _
    rw [List.map_cons, tr_and]
    set D := tr f φ ⋏ tr f ψ
    have pR := paramsVal_map_tr hH f Γ
    refine .and (OmegaPlus_mem hH _) (paramsVal_cons_sub pD pR) List.mem_cons_self
      (OmegaPlus_lt (show hgt dp < max (hgt dp) (hgt dq) + 1 by omega))
      (OmegaPlus_lt (show hgt dq < max (hgt dp) (hgt dq) + 1 by omega)) ?_ ?_
    · refine (ihp.mono_rank (OmegaPlus_le (le_max_left _ _))).weaken_seq hH.1
        (subset_cons_cons (List.subset_cons_self _ _)) ?_
      exact paramsVal_cons_sub (params_tr_sub hH f φ) (paramsVal_cons_sub pD pR)
    · refine (ihq.mono_rank (OmegaPlus_le (le_max_right _ _))).weaken_seq hH.1
        (subset_cons_cons (List.subset_cons_self _ _)) ?_
      exact paramsVal_cons_sub (params_tr_sub hH f ψ) (paramsVal_cons_sub pD pR)
  | _, @Derivation.all _ Γ φ d, f => by
    have pD : Stage.val '' params (∀¹ (numSubst₁ f ▹ embK φ)) ⊆ H ∅ := by
      rw [← tr_all]; exact params_tr_sub hH f _
    rw [List.map_cons, tr_all]
    set D := ∀¹ (numSubst₁ f ▹ embK φ)
    have pR := paramsVal_map_tr hH f Γ
    refine .all (fun _ => OmegaPlus (n := n) (hgt d)) (OmegaPlus_mem hH _)
      (paramsVal_cons_sub pD pR)
      List.mem_cons_self (fun _ => OmegaPlus_lt (Nat.lt_succ_self _)) (fun m' => ?_)
    have ih := replay hyps hX hH d (m' :>ₙ f)
    rw [List.map_cons, tr_free, tr_shifts] at ih
    refine ih.weaken_seq hH.1 (subset_cons_cons (List.subset_cons_self _ _)) ?_
    refine paramsVal_cons_sub ?_ (paramsVal_cons_sub pD pR)
    rw [params_subst, params_rew]; exact params_embK_sub hH φ
  | _, @Derivation.exs _ φ t Γ d, f => by
    have ih := replay hyps hX hH d f
    rw [List.map_cons, tr_subst] at ih
    have pD : Stage.val '' params (∃¹ (numSubst₁ f ▹ embK φ)) ⊆ H ∅ := by
      rw [← tr_exs]; exact params_tr_sub hH f _
    rw [List.map_cons, tr_exs]
    set φ' := numSubst₁ f ▹ embK φ with hφ'
    set D := ∃¹ φ'
    have pR := paramsVal_map_tr hH f Γ
    have ht : (numSubst f (Semiterm.lMap embedHom t)).freeVariables = ∅ :=
      freeVariables_numSubst_term' f _
    -- the witness is replaced by the numeral of *some* value `v`
    obtain ⟨v, ih'⟩ := hyps.replaceHeadNumI (φ' := φ')
      (numSubst f (Semiterm.lMap embedHom t)) (freeVariables_numSubst₁ f _) ht
      ((xFreeI_rew _ _).mpr (xFreeI_embK φ)) hX hH.1 ih
    refine .exs v (OmegaPlus_mem hH _)
      (paramsVal_cons_sub pD pR) List.mem_cons_self (ofNat_lt_OmegaPlus _ _)
      (OmegaPlus_lt (Nat.lt_succ_self _)) ?_
    refine ih'.weaken_seq hH.1 (subset_cons_cons (List.subset_cons_self _ _)) ?_
    refine paramsVal_cons_sub ?_ (paramsVal_cons_sub pD pR)
    rw [params_subst, hφ', params_rew]
    exact params_embK_sub hH φ
  | _, @Derivation.cut _ φ Γ Δ dp dn, f => by
    have ihp := replay hyps hX hH dp f
    have ihn := replay hyps hX hH dn f
    rw [List.map_cons] at ihp ihn
    rw [tr_neg] at ihn
    rw [List.map_append]
    have pR : paramsVal (Γ.map (tr f) ++ Δ.map (tr f)) ⊆ H ∅ := by
      rw [paramsVal_append]
      exact Set.union_subset (paramsVal_map_tr hH f Γ) (paramsVal_map_tr hH f Δ)
    have hρ : ∀ {j : ℕ}, j ≤ cutCx dp ∨ j ≤ cutCx dn →
        OmegaPlus (n := n) j ≤ OmegaPlus (n := n) (cutCx (Derivation.cut dp dn)) := by
      intro j hj
      refine OmegaPlus_le ?_
      show j ≤ max ((embK φ).complexity + 1) (max (cutCx dp) (cutCx dn))
      rcases hj with hj | hj <;> omega
    refine .cut (α₀ := OmegaPlus (n := n) (max (hgt dp) (hgt dn))) (OmegaPlus_mem hH _) pR
      (rk_tr_lt f φ (le_max_left _ _)) (OmegaPlus_lt (Nat.lt_succ_self _)) ?_ ?_
    · refine ((ihp.mono_rank (hρ (Or.inl le_rfl))).mono_height
        (OmegaPlus_le (le_max_left _ _)) (OmegaPlus_mem hH _)).weaken_seq hH.1
        (subset_cons_cons (List.subset_append_left _ _)) ?_
      exact paramsVal_cons_sub (params_tr_sub hH f φ) pR
    · refine ((ihn.mono_rank (hρ (Or.inr le_rfl))).mono_height
        (OmegaPlus_le (le_max_right _ _)) (OmegaPlus_mem hH _)).weaken_seq hH.1
        (subset_cons_cons (List.subset_append_right _ _)) ?_
      exact paramsVal_cons_sub (by rw [params_neg]; exact params_tr_sub hH f φ) pR

end Replay

/-! ### The axioms and their cut-away -/

section Main

/-- **Every axiom of `IDn n A`** is derivable, cut-free, at a height `Ω_n · 2 + m` (Freund,
proof of Theorem 6.5), dispatched to `EmbedHyps`. -/
theorem ax_derivable_of_mem (hyps : EmbedHyps A) (hA : FamilyPositive A)
    (hX : ∀ k, XFreeL (A k)) {θ : Sentence (LXIn n)} (h : θ ∈ ID A) : AxDerivable A θ := by
  rcases mem_ID A |>.mp h with h | h | h | ⟨k, rfl | ⟨F, rfl⟩⟩
  · exact hyps.eq_axiom h
  · exact hyps.paMinus_axiom h
  · exact hyps.induction_axiom hX h
  · exact hyps.closure_axiom k hX
  · exact hyps.indAx_axiom k (hA k) hX F

/-- A common height for finitely many axioms. -/
theorem axDerivable_list (Δ : List (Sentence (LXIn n))) (h : ∀ θ ∈ Δ, AxDerivable A θ) :
    ∃ N : ℕ, ∀ θ ∈ Δ, ∀ H : Set ThetaWNoteD → Set ThetaWNoteD, ThetaWNoteD.NiceS H →
      IDnDerivable A ThetaWNoteD.zero H (OmegaTwo (n := n) + ThetaWNoteD.ofNat N)
        [(Rewriting.emb (embK θ) : Proposition (LIinfN n))] := by
  induction Δ with
  | nil => exact ⟨0, fun θ hθ => absurd hθ (by simp)⟩
  | cons θ Δ ih =>
    obtain ⟨m, hm⟩ := h θ List.mem_cons_self
    obtain ⟨N, hN⟩ := ih fun θ' hθ' => h θ' (List.mem_cons_of_mem _ hθ')
    refine ⟨max m N, fun θ' hθ' H hH => ?_⟩
    have hmono : ∀ k, k ≤ max m N → OmegaTwo (n := n) + ThetaWNoteD.ofNat k ≤
        OmegaTwo (n := n) + ThetaWNoteD.ofNat (max m N) := fun k hk =>
      ThetaWNoteD.add_le_add_left _ (ThetaWNoteD.ofNat_le_ofNat hk)
    rcases List.mem_cons.mp hθ' with rfl | hθ'
    · exact (hm H hH).mono_height (hmono m (le_max_left _ _)) (OmegaTwo_mem hH _ _)
    · exact (hN θ' hθ' H hH).mono_height (hmono N (le_max_right _ _)) (OmegaTwo_mem hH _ _)

/-- A common bound for the complexities of finitely many embedded axioms. -/
theorem cx_list (Δ : List (Sentence (LXIn n))) :
    ∃ m : ℕ, ∀ θ ∈ Δ, (embK θ).complexity + 1 ≤ m := by
  induction Δ with
  | nil => exact ⟨0, fun θ hθ => absurd hθ (by simp)⟩
  | cons θ Δ ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨max ((embK θ).complexity + 1) m, fun θ' hθ' => ?_⟩
    rcases List.mem_cons.mp hθ' with rfl | hθ'
    · exact le_max_left _ _
    · exact le_trans (hm θ' hθ') (le_max_right _ _)

/-- **The parameters of the negated embedded axioms, over a whole list**: `paramsVal` unfolds
through `Stage.val '' paramsList`, not through a plain list membership (`x ∈ paramsVal (l.map g)`
destructures as some `s ∈ paramsList (l.map g)` with `x = Stage.val s`, *not* as `∃ a ∈ l, x ∈
params (g a)` the way a naive `List.mem_map` rewrite would expect), so this goes by induction on
the list instead, exactly as `paramsVal_map_tr` does for `tr f`. -/
private theorem paramsVal_negEmb_sub {H : Set ThetaWNoteD → Set ThetaWNoteD}
    (hH : ThetaWNoteD.NiceS H) (Δ : List (Sentence (LXIn n))) :
    paramsVal (Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition (LIinfN n)))) ⊆ H ∅ := by
  induction Δ with
  | nil => simp [paramsVal]
  | cons θ' Δ ih =>
    rw [List.map_cons, paramsVal_cons]
    refine Set.union_subset ?_ ih
    rw [params_neg, params_rew]
    exact params_embK_sub hH θ'

/-- **Cutting away the axioms**, one at a time (Freund, proof of Theorem 6.5): each cut is on
an embedded axiom of rank `≺ Ω_n + m`, against its derivation at height `Ω_n · 2 + N`. -/
theorem cut_axioms {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.NiceS H)
    {N m : ℕ} :
    ∀ (Δ : List (Sentence (LXIn n))),
      (∀ θ ∈ Δ, IDnDerivable A ThetaWNoteD.zero H (OmegaTwo (n := n) + ThetaWNoteD.ofNat N)
        [(Rewriting.emb (embK θ) : Proposition (LIinfN n))]) →
      (∀ θ ∈ Δ, (embK θ).complexity + 1 ≤ m) →
      ∀ {h : ℕ} {Θ : Sequent (LIinfN n)}, N ≤ h → paramsVal Θ ⊆ H ∅ →
        IDnDerivable A (OmegaPlus (n := n) m) H (OmegaTwo (n := n) + ThetaWNoteD.ofNat h)
          (Θ ++ Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition (LIinfN n)))) →
        IDnDerivable A (OmegaPlus (n := n) m) H
          (OmegaTwo (n := n) + ThetaWNoteD.ofNat (h + Δ.length)) Θ
  | [], _, _, h, Θ, _, _, d => by simpa using d
  | θ :: Δ, hax, hcx, h, Θ, hNh, hΘ, d => by
    set φ : Proposition (LIinfN n) := Rewriting.emb (embK θ) with hφ
    have pφ : Stage.val '' params φ ⊆ H ∅ := by rw [hφ, params_rew]; exact params_embK_sub hH θ
    have pRest : paramsVal (Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition (LIinfN n))))
        ⊆ H ∅ := paramsVal_negEmb_sub hH Δ
    have pΘR : paramsVal
        (Θ ++ Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition (LIinfN n)))) ⊆ H ∅ := by
      rw [paramsVal_append]; exact Set.union_subset hΘ pRest
    have hL : IDnDerivable A (OmegaPlus (n := n) m) H (OmegaTwo (n := n) + ThetaWNoteD.ofNat h)
        (∼φ :: (Θ ++ Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition (LIinfN n))))) :=
      d.weaken_seq hH.1 (by
        intro x hx
        simp only [List.map_cons, List.mem_append, List.mem_cons] at hx ⊢
        tauto) (paramsVal_cons_sub (by rw [params_neg]; exact pφ) pΘR)
    have hR : IDnDerivable A (OmegaPlus (n := n) m) H (OmegaTwo (n := n) + ThetaWNoteD.ofNat h)
        (φ :: (Θ ++ Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition (LIinfN n))))) :=
      (((hax θ List.mem_cons_self).mono_rank (ThetaWNoteD.zero_le' _)).mono_height
        (ThetaWNoteD.add_le_add_left _ (ThetaWNoteD.ofNat_le_ofNat hNh))
        (OmegaTwo_mem hH _ _)).weaken_seq hH.1
        (List.cons_subset_cons _ (List.nil_subset _)) (paramsVal_cons_sub pφ pΘR)
    have hrk : rk φ < OmegaPlus (n := n) m := by
      rw [hφ, rk_rew]
      exact lt_of_le_of_lt (rk_le_Omega_add_ofNat _) (OmegaPlus_lt (by
        have := hcx θ List.mem_cons_self; omega))
    have hcut : IDnDerivable A (OmegaPlus (n := n) m) H
        (OmegaTwo (n := n) + ThetaWNoteD.ofNat (h + 1))
        (Θ ++ Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition (LIinfN n)))) :=
      .cut (OmegaTwo_mem hH _ _) pΘR hrk
        (ThetaWNoteD.add_lt_add_left _ (ThetaWNoteD.ofNat_lt_ofNat (Nat.lt_succ_self h))) hR hL
    have key := cut_axioms hH Δ (fun θ' hθ' => hax θ' (List.mem_cons_of_mem _ hθ'))
      (fun θ' hθ' => hcx θ' (List.mem_cons_of_mem _ hθ')) (Nat.le_succ_of_le hNh) hΘ hcut
    rwa [show h + 1 + Δ.length = h + (θ :: Δ).length by simp; omega] at key

/-- **Freund, Theorem 6.5 (Embedding), per level.** If `IDn n A ⊢ σ`, then there are `m, r ∈ ℕ`
such that `H ⊢^{Ω_n·2+r}_{Ω_n+m} embed σ` for every operator `H` nice at level `n`. As in
`ID1.Embed`, this is stated with `X` read as empty (`embK`); for an `X`-free `σ`, `embK σ =
embed σ` (`embK_eq_embed`). -/
theorem embedding_theorem (hyps : EmbedHyps A) (hA : FamilyPositive A) (hX : ∀ k, XFreeL (A k))
    {σ : Sentence (LXIn n)} (h : ID A ⊢ σ) :
    ∃ m r : ℕ, ∀ H : Set ThetaWNoteD → Set ThetaWNoteD, ThetaWNoteD.NiceS H →
      IDnDerivable A (OmegaPlus (n := n) m) H (OmegaTwo (n := n) + ThetaWNoteD.ofNat r)
        [(Rewriting.emb (embK σ) : Proposition (LIinfN n))] := by
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := Theory.Proof.provable_iff.mp h
  have hax : ∀ θ ∈ Δ, AxDerivable A θ := fun θ hθ => ax_derivable_of_mem hyps hA hX (hΔ θ hθ)
  obtain ⟨N, hN⟩ := axDerivable_list Δ hax
  obtain ⟨m0, hm0⟩ := cx_list Δ
  refine ⟨max (cutCx d) m0, max (hgt d) N + Δ.length, fun H hH => ?_⟩
  have r := replay hyps hX hH d (fun _ => 0)
  have e : ((σ : Proposition (LXIn n)) :: ∼Sequent.embed Δ).map (tr (fun _ => 0)) =
      [(Rewriting.emb (embK σ) : Proposition (LIinfN n))] ++
        Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition (LIinfN n))) := by
    rw [List.map_cons, tr_emb, List.singleton_append, List.tilde_def, Sequent.embed,
      List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun θ _ => ?_
    simp only [Function.comp_apply, tr_neg, tr_emb]
  rw [e] at r
  refine cut_axioms hH Δ (fun θ hθ => hN θ hθ H hH)
    (fun θ hθ => le_trans (hm0 θ hθ) (le_max_right _ _)) (le_max_right _ _)
    (paramsVal_cons_sub (paramsVal_of_params_sub hH ((params_rew _ _).le.trans
      (params_embK σ))) (by simp)) ?_
  refine (r.mono_rank (OmegaPlus_le (le_max_left _ _))).mono_height ?_ (OmegaTwo_mem hH _ _)
  -- `Ω_n + hgt d ≤ (Ω_n + Ω_n) + max (hgt d) N`: no left-monotonicity of `+` is needed (`add`
  -- is not commutative and no such lemma is proved for it), only right-monotonicity plus
  -- `le_add_left` (`b ≤ a + b`) after `add_assoc` regroups the right-hand side.
  show OmegaPlus (n := n) (hgt d) ≤ OmegaTwo (n := n) + ThetaWNoteD.ofNat (max (hgt d) N)
  rw [OmegaTwo, ThetaWNoteD.add_assoc]
  exact ThetaWNoteD.add_le_add_left _ (le_trans
    (ThetaWNoteD.ofNat_le_ofNat (le_max_left _ _)) (ThetaWNoteD.le_add_left _ _))

/-- **Theorem 6.5 for `X`-free sentences**, in Freund's per-level form: `H ⊢^{Ω_n·2+r}_{Ω_n+m}
σ⁺` with `σ⁺ = embed σ` (`I_k ↦ I_k^{≺Ω_{k+1}}`). -/
theorem embedding_theorem_xfree (hyps : EmbedHyps A) (hA : FamilyPositive A)
    (hX : ∀ k, XFreeL (A k)) {σ : Sentence (LXIn n)} (hσ : XFreeL σ) (h : ID A ⊢ σ) :
    ∃ m r : ℕ, ∀ H : Set ThetaWNoteD → Set ThetaWNoteD, ThetaWNoteD.NiceS H →
      IDnDerivable A (OmegaPlus (n := n) m) H (OmegaTwo (n := n) + ThetaWNoteD.ofNat r)
        [embed (σ : Proposition (LXIn n))] := by
  obtain ⟨m, r, hmr⟩ := embedding_theorem hyps hA hX h
  refine ⟨m, r, fun H hH => ?_⟩
  have e : embed (σ : Proposition (LXIn n)) = (Rewriting.emb (embK σ) : Proposition (LIinfN n)) := by
    rw [embK_eq_embed hσ]; exact Semiformula.lMap_emb σ
  rw [e]; exact hmr H hH

end Main

end IDn

end OrdinalAnalysis

