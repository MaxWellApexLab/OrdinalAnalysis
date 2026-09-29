/- Source: OrdinalAnalysis/IDn/Embed.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega;
  the design notes "Embedding"). Freund arXiv:2204.09321 Thm 6.5, uniform.

  **Statement.** `IDw A ⊢ σ ⇒ ∃ m r, ∀ H, NiceS H → IDwDerivable A (Ω_ω + m) H (Ω_ω·2 + r) [embK σ]`
  (`OmegaPlus m := OmegaW + ofNat m` is the cut rank, `OmegaTwo + ofNat r := OmegaW + OmegaW +
  ofNat r` the height; IDn's `Ω_n + m`, `Ω_n·2 + r`).

  Deviations from the IDn file, forced by the ID_ω calculus:

  * `IDn/{AxiomsLogic,AxiomsPA,AxiomsID}` are still in flight for `IDw`, so the axiom lemmas
    are fields of **`EmbedHyps`**, exactly as in IDn (`taut`, `eq_axiom`, `paMinus_axiom`,
    `induction_axiom`, `closure_axiom`, `indAx_axiom`), now stated for the single formula
    `A : FormJ` and the two ID_ω axiom schemes `closureAxJ A`, `indAxJ A F` (`PositiveP A` is
    the hypothesis of the last two). `IDw.Evaluate` *is* on disk, so the IDn field
    `replaceHeadNumI` is now a proved theorem (`replaceHeadNumI`, from `IDwDerivable.replace_head`
    and `sim_subst_numI`) and no field. `AxDerivable` itself needs no hypothesis.
  * `IDw`'s operator form is one `A : FormJ` over `LForm` (only `P`, `Q`; no `X`), so the
    `XFreeL (A k)` hypotheses of IDn (`hX`) are gone, and `FamilyPositive A` is `PositiveP A`.
  * **The heights are the by-hand part.** IDn's `Ω_n` becomes `Ω_ω = OmegaW`. There is no finite
    top level to bound `rk φ` by any more: the generic finite-part bound `rk_le_add_ofNat` is
    not ported (`IDw/Rank.lean`: false for bare `Jlev ⊤` atoms as stated), so the rank bound
    `rk φ ≤ Ω_ω + complexity φ` (`rk_le_OmegaW_add_ofNat`) is proved here directly for *every*
    `φ : Semiformula LIinfW ξ m`: a stage atom has rank `< Ω_ω`, `Jlev ℓ` has rank `≤ Ω_ω`.
    The additive principality of `Ω_ω` (`ThetaVTerm.isPrin_OmegaW`) gives `ω · x ≤ Ω_ω` for
    `x ≤ Ω_ω` (`omegaMul_OmegaW`), needed for `EmbedHyps.taut`'s `omegaMul (rk ψ)` height.
    `params (tr f φ) = ∅` (`params_tr`, `= ∅` rather than IDn's `⊆ {tops}`) makes every
    parameter side condition of the replay vacuous.
  * `ThetaVNoteD.NiceS` (`Ordinal/ThetaV/HullSingle.lean`) is the level-free nice operator, as
    `ThetaWNoteD.NiceS` in IDn; `NiceS.OmegaW_mem` replaces `Omega_mem (n-1)`.

  Contents.

    `EmbedHyps`                          the axiom lemmas, as hypotheses
    `AxDerivable`, `OmegaTwo`            self-contained (no hypothesis needed)
    `hgt`, `cutCx`                       height and cut complexity of an `LK` derivation
    `tr_*`, `rk_le_OmegaW_add_ofNat`     the translation under an assignment, and its rank bound
    `replay`                             **the replay**
    `ax_derivable_of_mem`                every axiom of `IDw A`, dispatched to `EmbedHyps`
    `cut_axioms`                         cutting away the axioms
    `embedding_theorem`                  **Theorem 6.5**
-/
import OrdinalAnalysis.IDw.NumSubst
import OrdinalAnalysis.IDw.Evaluate
import OrdinalAnalysis.IDw.ReductionAux
import OrdinalAnalysis.IDw.Rank
import OrdinalAnalysis.Ordinal.Collapsing.Limit

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting
open LO.FirstOrder.Arithmetic

/-! ### `AxDerivable`, self-contained -/

section AxDerivable

variable (A : FormJ)

/-- `Ω_ω · 2` (`OmegaW + OmegaW`), the height at which every axiom of `IDw A` is cut-free
derivable (Freund, proof of Theorem 6.5; IDn's `Ω_ω · 2`). -/
abbrev OmegaTwo : ThetaVNoteD := ThetaVNoteD.OmegaW + ThetaVNoteD.OmegaW

theorem OmegaTwo_mem {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.NiceS H)
    (X : Set ThetaVNoteD) (m : ℕ) : OmegaTwo + ThetaVNoteD.ofNat m ∈ H X :=
  hH.add_mem (hH.add_mem hH.OmegaW_mem hH.OmegaW_mem) (hH.ofNat_mem m)

/-- **The axiom `σ` is derivable** in the form of Freund, proof of Theorem 6.5: cut-free, at
a height `Ω_ω · 2 + m` independent of the nice operator. -/
def AxDerivable (σ : Sentence LXJ) : Prop :=
  ∃ m : ℕ, ∀ H : Set ThetaVNoteD → Set ThetaVNoteD, ThetaVNoteD.NiceS H →
    IDwDerivable A ThetaVNoteD.zero H (OmegaTwo + ThetaVNoteD.ofNat m)
      [(Rewriting.emb (embK σ) : Proposition LIinfW)]

theorem axDerivable_of_le {σ : Sentence LXJ} (m : ℕ) (β : ThetaVNoteD)
    (hβ : β ≤ OmegaTwo + ThetaVNoteD.ofNat m)
    (h : ∀ H : Set ThetaVNoteD → Set ThetaVNoteD, ThetaVNoteD.NiceS H →
      IDwDerivable A ThetaVNoteD.zero H β [(Rewriting.emb (embK σ) : Proposition LIinfW)]) :
    AxDerivable A σ :=
  ⟨m, fun H hH => (h H hH).mono_height hβ (OmegaTwo_mem hH _ _)⟩

end AxDerivable

/-! ### `EmbedHyps`: the axiom lemmas, not yet available on disk -/

/-- **What `replay`/`ax_derivable_of_mem` need from `IDw/{AxiomsLogic,AxiomsPA,AxiomsIDCases}`**
(in flight): each field is the statement of a real theorem of Freund's Section 6 for `ID_ω`,
taken as a hypothesis so that this file does not wait for them. Term replacement (IDn's
`replaceHeadNumI` field) is proved below from `IDw.Evaluate` and is no field. -/
structure EmbedHyps (A : FormJ) where
  /-- **Freund, Lemma 6.1** (`IDw.AxiomsLogic.taut`): a closed formula and its negation are
  derivable together, cut-free, at height `ω` times its own rank — *not* `rk ψ` itself (that
  version is refuted by `IDn.taut_additive_impossible`, witness `ψ = ∀x. X(x)`). -/
  taut : ∀ {H : Set ThetaVNoteD → Set ThetaVNoteD}, ThetaVNoteD.NiceS H →
    ∀ ψ : Proposition LIinfW, ψ.freeVariables = ∅ →
      IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params ψ))
        (ThetaVNoteD.omegaMul (rk ψ)) [ψ, ∼ψ]
  /-- **The equality axioms**. -/
  eq_axiom : ∀ {σ : Sentence LXJ}, σ ∈ 𝗘𝗤 LXJ → AxDerivable A σ
  /-- **The `𝗣𝗔⁻` axioms**. -/
  paMinus_axiom : ∀ {σ : Sentence LXJ}, σ ∈ Theory.lMap toLXJ 𝗣𝗔⁻ → AxDerivable A σ
  /-- **Every induction axiom of the whole language**. -/
  induction_axiom : ∀ {σ : Sentence LXJ}, σ ∈ InductionScheme LXJ Set.univ → AxDerivable A σ
  /-- **The closure axiom** `closureAxJ A` (`IDw.AxiomsIDCases`). -/
  closure_axiom : PositiveP A → AxDerivable A (closureAxJ A)
  /-- **The induction axiom scheme** `indAxJ A F` (`IDw.AxiomsIDCases`). -/
  indAx_axiom : PositiveP A → ∀ F : Semiformula LXJ ℕ 2, AxDerivable A (indAxJ A F)

/-- **Term replacement at the head, specialised to a numeral witness** (`IDwDerivable.replace_head`
composed with `sim_subst_numI`, the step Freund's proof of Proposition 6.4 uses for `∃`): a
closed term `t` in the head formula's substitution slot may be replaced by the numeral of its
value, for *some* value `v`. (A field of `IDn.EmbedHyps` while `Evaluate` was red.) -/
theorem replaceHeadNumI {ρ : ThetaVNoteD} {H : Set ThetaVNoteD → Set ThetaVNoteD}
    {α : ThetaVNoteD} {A : FormJ} {Γ : Sequent LIinfW} {φ' : Semiformula LIinfW ℕ 1}
    (t : SyntacticTerm LIinfW) (hφ : φ'.freeVariables = ∅) (ht : t.freeVariables = ∅)
    (hx : XFreeI φ') (hH : ThetaVNoteD.IsOperator H)
    (d : IDwDerivable A ρ H α (φ'/[t] :: Γ)) :
    ∃ v : ℕ, IDwDerivable A ρ H α (φ'/[numI v] :: Γ) :=
  ⟨closedVal t, d.replace_head hH (sim_subst_numI hφ hx ht)⟩

/-! ### Height and cut complexity of a finitary derivation -/

variable {A : FormJ}

/-- The height of the replay of an `LK` derivation, above `Ω_ω`. -/
def hgt : {Γ : Sequent LXJ} → ⊢ᴸᴷ¹ Γ → ℕ
  | _, Derivation.identity _ _ => 0
  | _, Derivation.verum => 0
  | _, Derivation.cut dp dn => max (hgt dp) (hgt dn) + 1
  | _, Derivation.contraction d _ => hgt d
  | _, Derivation.or d => hgt d + 2
  | _, Derivation.and dp dq => max (hgt dp) (hgt dq) + 1
  | _, Derivation.all d => hgt d + 1
  | _, Derivation.exs d => hgt d + 1

/-- One more than the largest complexity of an embedded cut formula. -/
def cutCx : {Γ : Sequent LXJ} → ⊢ᴸᴷ¹ Γ → ℕ
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

theorem tr_or (f : ℕ → ℕ) (φ ψ : Proposition LXJ) : tr f (φ ⋎ ψ) = tr f φ ⋎ tr f ψ := by
  simp [tr]

theorem tr_and (f : ℕ → ℕ) (φ ψ : Proposition LXJ) : tr f (φ ⋏ ψ) = tr f φ ⋏ tr f ψ := by
  simp [tr]

theorem tr_verum (f : ℕ → ℕ) : tr f ⊤ = (⊤ : Proposition LIinfW) := by simp [tr]

theorem tr_all (f : ℕ → ℕ) (φ : Semiproposition LXJ 1) :
    tr f (∀¹ φ) = ∀¹ (numSubst₁ f ▹ embK φ) := by
  rw [tr, embK_all, numSubst_all]

theorem tr_exs (f : ℕ → ℕ) (φ : Semiproposition LXJ 1) :
    tr f (∃¹ φ) = ∃¹ (numSubst₁ f ▹ embK φ) := by
  rw [tr, embK_exs, numSubst_exs]

theorem tr_free (f : ℕ → ℕ) (m : ℕ) (φ : Semiproposition LXJ 1) :
    tr (m :>ₙ f) (Rewriting.free φ) = (numSubst₁ f ▹ embK φ)/[numI m] := by
  rw [tr, embK_free, numSubst_free]

theorem tr_shifts (f : ℕ → ℕ) (m : ℕ) (Γ : Sequent LXJ) :
    (Γ⁺).map (tr (m :>ₙ f)) = Γ.map (tr f) := by
  induction Γ with
  | nil => rfl
  | cons φ Γ ih =>
    rw [Rewriting.shifts_cons, List.map_cons, List.map_cons, ih, tr, tr, embK_shift,
      numSubst_shift]

theorem tr_subst (f : ℕ → ℕ) (φ : Semiproposition LXJ 1) (t : SyntacticTerm LXJ) :
    tr f (φ/[t]) = (numSubst₁ f ▹ embK φ)/[numSubst f (Semiterm.lMap embedW t)] := by
  rw [tr, embK_subst₁, numSubst_subst]

/-- **Formulas without stage parameters have `Stage.val ''` params inside any `H ∅`**: `IDn`'s
`paramsVal_of_params_sub` (parameters all level-tops) specialised to the case the embedding
actually meets, `params φ = ∅` (`params_embK`, `params_tr`: the embedding produces only `X` and
`Jlev` atoms). -/
theorem paramsVal_of_params_eq {H : Set ThetaVNoteD → Set ThetaVNoteD}
    {ξ : Type*} {m : ℕ} {φ : Semiformula LIinfW ξ m}
    (h : params φ = ∅) : Stage.val '' params φ ⊆ H ∅ := by
  rw [h, Set.image_empty]; exact Set.empty_subset _

theorem params_tr_sub {H : Set ThetaVNoteD → Set ThetaVNoteD}
    (f : ℕ → ℕ) (φ : Proposition LXJ) : Stage.val '' params (tr f φ) ⊆ H ∅ :=
  paramsVal_of_params_eq (params_tr f φ)

theorem params_embK_sub {H : Set ThetaVNoteD → Set ThetaVNoteD}
    {ξ : Type*} {m : ℕ} (φ : Semiformula LXJ ξ m) : Stage.val '' params (embK φ) ⊆ H ∅ :=
  paramsVal_of_params_eq (params_embK φ)

theorem paramsVal_map_tr {H : Set ThetaVNoteD → Set ThetaVNoteD}
    (f : ℕ → ℕ) (Γ : Sequent LXJ) : paramsVal (Γ.map (tr f)) ⊆ H ∅ := by
  induction Γ with
  | nil => simp [paramsVal]
  | cons φ Γ ih =>
    rw [List.map_cons, paramsVal_cons]
    exact Set.union_subset (params_tr_sub f φ) ih

theorem paramsVal_cons_sub {H : Set ThetaVNoteD → Set ThetaVNoteD} {φ : Proposition LIinfW}
    {Γ : Sequent LIinfW} (h1 : Stage.val '' params φ ⊆ H ∅) (h2 : paramsVal Γ ⊆ H ∅) :
    paramsVal (φ :: Γ) ⊆ H ∅ := by
  rw [paramsVal_cons]; exact Set.union_subset h1 h2

/-- **The atom rank is at most `Ω_ω`**: a stage atom `I_k^{≺a}` has rank `Ω_k + ω·a < Ω_ω`
(additive principality of `Ω_ω`), `Jlev k` has rank `Ω_k + 1 < Ω_ω`, `Jlev ⊤` has rank `Ω_ω`. -/
theorem atomRk_le_OmegaW {k : ℕ} (r : LIinfW.Rel k) : atomRk r ≤ ThetaVNoteD.OmegaW := by
  rcases r with r | r
  · exact ThetaVNoteD.zero_le' _
  · cases r with
    | X => exact ThetaVNoteD.zero_le' _
    | stage s =>
      refine le_of_lt ?_
      show atomRkStage s < ThetaVNoteD.OmegaW
      exact ThetaVNoteD.add_lt_prin trivial (ThetaVNoteD.OmegaBelow_lt_OmegaW s.lvl)
        (lt_of_le_of_lt (ThetaVNoteD.omegaMul_le_omegaMul s.le)
          (by rw [ThetaVNoteD.omegaMul_Omega]; exact ThetaVNoteD.Omega_lt_OmegaW s.lvl))
    | jlev ℓ =>
      show atomRkJlev ℓ ≤ ThetaVNoteD.OmegaW
      induction ℓ using WithTop.recTopCoe with
      | top => rw [atomRkJlev_top]
      | coe j =>
        exact le_of_lt (ThetaVNoteD.succ_lt_prin trivial (ThetaVNoteD.OmegaBelow_lt_OmegaW j))

/-- **Every formula of `LIinfW` has rank at most `Ω_ω + complexity`** (the `Ω_ω` version of
`IDn.rk_le_Omega_add_ofNat`, proved directly, without the finite-part bound `rk_le_add_ofNat`,
which `IDw.Rank` does not port). -/
theorem rk_le_OmegaW_add_ofNat {ξ : Type*} {m : ℕ} (φ : Semiformula LIinfW ξ m) :
    rk φ ≤ ThetaVNoteD.OmegaW + ThetaVNoteD.ofNat φ.complexity := by
  induction φ using Semiformula.rec' with
  | hverum => rw [rk_verum]; exact ThetaVNoteD.zero_le' _
  | hfalsum => rw [rk_falsum]; exact ThetaVNoteD.zero_le' _
  | hrel r v =>
    rw [rk_rel]; exact le_trans (atomRk_le_OmegaW r) (ThetaVNoteD.le_add_right _ _)
  | hnrel r v =>
    rw [rk_nrel]; exact le_trans (atomRk_le_OmegaW r) (ThetaVNoteD.le_add_right _ _)
  | hand φ ψ ihφ ihψ =>
    rw [rk_and, Semiformula.complexity_and, ← ThetaVNoteD.succ_add_ofNat]
    refine ThetaVNoteD.succ_le_succ (max_le ?_ ?_)
    · exact le_trans ihφ (ThetaVNoteD.add_le_add_left _
        (ThetaVNoteD.ofNat_le_ofNat (le_max_left _ _)))
    · exact le_trans ihψ (ThetaVNoteD.add_le_add_left _
        (ThetaVNoteD.ofNat_le_ofNat (le_max_right _ _)))
  | hor φ ψ ihφ ihψ =>
    rw [rk_or, Semiformula.complexity_or, ← ThetaVNoteD.succ_add_ofNat]
    refine ThetaVNoteD.succ_le_succ (max_le ?_ ?_)
    · exact le_trans ihφ (ThetaVNoteD.add_le_add_left _
        (ThetaVNoteD.ofNat_le_ofNat (le_max_left _ _)))
    · exact le_trans ihψ (ThetaVNoteD.add_le_add_left _
        (ThetaVNoteD.ofNat_le_ofNat (le_max_right _ _)))
  | hall φ ih =>
    rw [rk_all, Semiformula.complexity_all, ← ThetaVNoteD.succ_add_ofNat]
    exact ThetaVNoteD.succ_le_succ ih
  | hexs φ ih =>
    rw [rk_exs, Semiformula.complexity_exs, ← ThetaVNoteD.succ_add_ofNat]
    exact ThetaVNoteD.succ_le_succ ih

/-- The embedded formula of an atom has rank at most `Ω_ω`: its complexity is `0`. -/
theorem rk_tr_atom_le (f : ℕ → ℕ) {k : ℕ} (r : LXJ.Rel k)
    (v : Fin k → SyntacticTerm LXJ) :
    rk (tr f (Semiformula.rel r v)) ≤ ThetaVNoteD.OmegaW := by
  have hc : (tr f (Semiformula.rel r v)).complexity = 0 := by
    rw [tr, Semiformula.complexity_rew]
    rcases r with r | r
    · rfl
    · cases r <;> rfl
  have h := rk_le_OmegaW_add_ofNat (tr f (Semiformula.rel r v))
  rwa [hc, ThetaVNoteD.ofNat_zero, ThetaVNoteD.add_zero] at h

/-- **`ω · rk` of the embedded atom's translation is still `≤ Ω_ω`**: `rk_tr_atom_le` gives
`rk (tr f atom) ≤ Ω_ω`, and `Ω_ω` (principal, `isPrin_OmegaW`) absorbs `ω · ·` from at-or-below
(`omegaMul_lt_prin` from below, `omegaMul_OmegaW` at equality). Needed because `EmbedHyps.taut`'s
height is `omegaMul (rk ψ)`, not `rk ψ` (`taut_additive_impossible` refutes the additive
version). -/
theorem omegaMul_rk_tr_atom_le (f : ℕ → ℕ) {k : ℕ} (r : LXJ.Rel k)
    (v : Fin k → SyntacticTerm LXJ) :
    ThetaVNoteD.omegaMul (rk (tr f (Semiformula.rel r v))) ≤ ThetaVNoteD.OmegaW := by
  rcases (rk_tr_atom_le f r v).lt_or_eq with h | h
  · exact (ThetaVNoteD.omegaMul_lt_prin (p := ThetaVNoteD.OmegaW) trivial h).le
  · rw [h, ThetaVNoteD.omegaMul_OmegaW]

theorem rk_tr_lt (f : ℕ → ℕ) (φ : Proposition LXJ) {m : ℕ}
    (hm : (embK φ).complexity + 1 ≤ m) :
    rk (tr f φ) < ThetaVNoteD.OmegaW + ThetaVNoteD.ofNat m := by
  refine lt_of_le_of_lt (rk_le_OmegaW_add_ofNat _) (ThetaVNoteD.add_lt_add_left _
    (ThetaVNoteD.ofNat_lt_ofNat ?_))
  rw [tr, Semiformula.complexity_rew]; omega

end Tr

/-! ### The replay -/

section Replay

variable {H : Set ThetaVNoteD → Set ThetaVNoteD}

/-- `Ω_ω + j` (`OmegaW + ofNat j`; IDn's `Ω_ω + j`): every embedded formula has rank
`≤ Ω_ω + complexity`, `rk_le_OmegaW_add_ofNat`. -/
abbrev OmegaPlus (j : ℕ) : ThetaVNoteD := ThetaVNoteD.OmegaW + ThetaVNoteD.ofNat j

theorem OmegaPlus_mem (hH : ThetaVNoteD.NiceS H) (j : ℕ) : OmegaPlus j ∈ H ∅ :=
  hH.add_mem hH.OmegaW_mem (hH.ofNat_mem j)

theorem OmegaPlus_lt {j k : ℕ} (h : j < k) : OmegaPlus j < OmegaPlus k :=
  ThetaVNoteD.add_lt_add_left _ (ThetaVNoteD.ofNat_lt_ofNat h)

theorem OmegaPlus_le {j k : ℕ} (h : j ≤ k) : OmegaPlus j ≤ OmegaPlus k :=
  ThetaVNoteD.add_le_add_left _ (ThetaVNoteD.ofNat_le_ofNat h)

theorem one_lt_OmegaPlus (j : ℕ) : ThetaVNoteD.one < OmegaPlus j :=
  lt_of_lt_of_le (ThetaVNoteD.one_lt_prin (p := ThetaVNoteD.OmegaW) trivial)
    (ThetaVNoteD.le_add_right _ _)

theorem ofNat_lt_OmegaPlus (m j : ℕ) : ThetaVNoteD.ofNat m < OmegaPlus j :=
  lt_of_lt_of_le (ThetaVNoteD.ofNat_lt_prin (p := ThetaVNoteD.OmegaW) trivial m)
    (ThetaVNoteD.le_add_right _ _)

theorem subset_cons_cons {α : Type*} {a : α} {Γ Δ : List α} (h : Γ ⊆ Δ) : a :: Γ ⊆ a :: Δ :=
  List.cons_subset_cons a h

/-- **The replay** (Freund, proof of Theorem 6.5): an `LK` derivation of `Γ` gives, for every
assignment `f` of numerals to the free variables, a derivation of the embedded sequent at
height `Ω_ω + h` and cut rank `Ω_ω + m`, with `h`, `m` read off the derivation. -/
theorem replay (hyps : EmbedHyps A) (hH : ThetaVNoteD.NiceS H) :
    ∀ {Γ : Sequent LXJ} (d : ⊢ᴸᴷ¹ Γ) (f : ℕ → ℕ),
      IDwDerivable A (OmegaPlus (cutCx d)) H (OmegaPlus (hgt d)) (Γ.map (tr f))
  | _, Derivation.identity r v, f => by
    have hc : (tr f (Semiformula.rel r v)).freeVariables = ∅ := freeVariables_tr f _
    have d := hyps.taut hH (tr f (Semiformula.rel r v)) hc
    rw [ThetaVNoteD.adjoin_eq_self hH.1 (params_tr_sub f _)] at d
    have e : [Semiformula.rel r v, Semiformula.nrel r v].map (tr f) =
        [tr f (Semiformula.rel r v), ∼(tr f (Semiformula.rel r v))] := by
      rw [List.map_cons, List.map_cons, List.map_nil, ← tr_neg, Semiformula.neg_rel]
    rw [e]
    refine (d.mono_rank (ThetaVNoteD.zero_le' _)).mono_height ?_ (OmegaPlus_mem hH _)
    show ThetaVNoteD.omegaMul (rk (tr f (Semiformula.rel r v))) ≤
      ThetaVNoteD.OmegaW + ThetaVNoteD.ofNat 0
    rw [ThetaVNoteD.ofNat_zero, ThetaVNoteD.add_zero]
    exact omegaMul_rk_tr_atom_le f r v
  | _, Derivation.verum, f => by
    rw [List.map_cons, List.map_nil, tr_verum]
    exact .verum (OmegaPlus_mem hH _) (paramsVal_cons_sub (by simp) (by simp))
      List.mem_cons_self
  | _, Derivation.contraction d ss, f =>
    (replay hyps hH d f).weaken_seq hH.1 (List.map_subset _ ss)
      (paramsVal_map_tr (H := H) f _)
  | _, @Derivation.or _ φ ψ Γ d, f => by
    have ih := replay hyps hH d f
    rw [List.map_cons, List.map_cons] at ih
    have pD : Stage.val '' params (tr f φ ⋎ tr f ψ) ⊆ H ∅ := by
      rw [← tr_or]; exact params_tr_sub f _
    rw [List.map_cons, tr_or]
    set D := tr f φ ⋎ tr f ψ
    have pR := paramsVal_map_tr (H := H) f Γ
    have e1 : IDwDerivable A (OmegaPlus (cutCx d)) H (OmegaPlus (hgt d + 1))
        (tr f φ :: D :: Γ.map (tr f)) :=
      .orR (OmegaPlus_mem hH _) (paramsVal_cons_sub (params_tr_sub f φ)
          (paramsVal_cons_sub pD pR)) (List.mem_cons_of_mem _ List.mem_cons_self)
        (one_lt_OmegaPlus _) (OmegaPlus_lt (Nat.lt_succ_self _))
        (ih.weaken_seq hH.1 (by
          intro x hx; simp only [List.mem_cons] at hx ⊢; tauto)
          (paramsVal_cons_sub (params_tr_sub f ψ) (paramsVal_cons_sub
            (params_tr_sub f φ) (paramsVal_cons_sub pD pR))))
    exact .orL (OmegaPlus_mem hH _) (paramsVal_cons_sub pD pR) List.mem_cons_self
      (OmegaPlus_lt (show hgt d + 1 < hgt d + 2 by omega)) e1
  | _, @Derivation.and _ φ Γ ψ dp dq, f => by
    have ihp := replay hyps hH dp f
    have ihq := replay hyps hH dq f
    rw [List.map_cons] at ihp ihq
    have pD : Stage.val '' params (tr f φ ⋏ tr f ψ) ⊆ H ∅ := by
      rw [← tr_and]; exact params_tr_sub f _
    rw [List.map_cons, tr_and]
    set D := tr f φ ⋏ tr f ψ
    have pR := paramsVal_map_tr (H := H) f Γ
    refine .and (OmegaPlus_mem hH _) (paramsVal_cons_sub pD pR) List.mem_cons_self
      (OmegaPlus_lt (show hgt dp < max (hgt dp) (hgt dq) + 1 by omega))
      (OmegaPlus_lt (show hgt dq < max (hgt dp) (hgt dq) + 1 by omega)) ?_ ?_
    · refine (ihp.mono_rank (OmegaPlus_le (le_max_left _ _))).weaken_seq hH.1
        (subset_cons_cons (List.subset_cons_self _ _)) ?_
      exact paramsVal_cons_sub (params_tr_sub f φ) (paramsVal_cons_sub pD pR)
    · refine (ihq.mono_rank (OmegaPlus_le (le_max_right _ _))).weaken_seq hH.1
        (subset_cons_cons (List.subset_cons_self _ _)) ?_
      exact paramsVal_cons_sub (params_tr_sub f ψ) (paramsVal_cons_sub pD pR)
  | _, @Derivation.all _ Γ φ d, f => by
    have pD : Stage.val '' params (∀¹ (numSubst₁ f ▹ embK φ)) ⊆ H ∅ := by
      rw [← tr_all]; exact params_tr_sub f _
    rw [List.map_cons, tr_all]
    set D := ∀¹ (numSubst₁ f ▹ embK φ)
    have pR := paramsVal_map_tr (H := H) f Γ
    refine .all (fun _ => OmegaPlus (hgt d)) (OmegaPlus_mem hH _)
      (paramsVal_cons_sub pD pR)
      List.mem_cons_self (fun _ => OmegaPlus_lt (Nat.lt_succ_self _)) (fun m' => ?_)
    have ih := replay hyps hH d (m' :>ₙ f)
    rw [List.map_cons, tr_free, tr_shifts] at ih
    refine ih.weaken_seq hH.1 (subset_cons_cons (List.subset_cons_self _ _)) ?_
    refine paramsVal_cons_sub ?_ (paramsVal_cons_sub pD pR)
    rw [params_subst1, params_rew]; exact params_embK_sub φ
  | _, @Derivation.exs _ φ t Γ d, f => by
    have ih := replay hyps hH d f
    rw [List.map_cons, tr_subst] at ih
    have pD : Stage.val '' params (∃¹ (numSubst₁ f ▹ embK φ)) ⊆ H ∅ := by
      rw [← tr_exs]; exact params_tr_sub f _
    rw [List.map_cons, tr_exs]
    set φ' := numSubst₁ f ▹ embK φ with hφ'
    set D := ∃¹ φ'
    have pR := paramsVal_map_tr (H := H) f Γ
    have ht : (numSubst f (Semiterm.lMap embedW t)).freeVariables = ∅ :=
      freeVariables_numSubst_term' f _
    -- the witness is replaced by the numeral of *some* value `v`
    obtain ⟨v, ih'⟩ := replaceHeadNumI (φ' := φ')
      (numSubst f (Semiterm.lMap embedW t)) (freeVariables_numSubst₁ f _) ht
      ((xFreeI_rew _ _).mpr (xFreeI_embK φ)) hH.1 ih
    refine .exs v (OmegaPlus_mem hH _)
      (paramsVal_cons_sub pD pR) List.mem_cons_self (ofNat_lt_OmegaPlus _ _)
      (OmegaPlus_lt (Nat.lt_succ_self _)) ?_
    refine ih'.weaken_seq hH.1 (subset_cons_cons (List.subset_cons_self _ _)) ?_
    refine paramsVal_cons_sub ?_ (paramsVal_cons_sub pD pR)
    rw [params_subst1, hφ', params_rew]
    exact params_embK_sub φ
  | _, @Derivation.cut _ φ Γ Δ dp dn, f => by
    have ihp := replay hyps hH dp f
    have ihn := replay hyps hH dn f
    rw [List.map_cons] at ihp ihn
    rw [tr_neg] at ihn
    rw [List.map_append]
    have pR : paramsVal (Γ.map (tr f) ++ Δ.map (tr f)) ⊆ H ∅ := by
      rw [paramsVal_append]
      exact Set.union_subset (paramsVal_map_tr (H := H) f Γ) (paramsVal_map_tr (H := H) f Δ)
    have hρ : ∀ {j : ℕ}, j ≤ cutCx dp ∨ j ≤ cutCx dn →
        OmegaPlus j ≤ OmegaPlus (cutCx (Derivation.cut dp dn)) := by
      intro j hj
      refine OmegaPlus_le ?_
      show j ≤ max ((embK φ).complexity + 1) (max (cutCx dp) (cutCx dn))
      rcases hj with hj | hj <;> omega
    refine .cut (α₀ := OmegaPlus (max (hgt dp) (hgt dn))) (OmegaPlus_mem hH _) pR
      (rk_tr_lt f φ (le_max_left _ _)) (OmegaPlus_lt (Nat.lt_succ_self _)) ?_ ?_
    · refine ((ihp.mono_rank (hρ (Or.inl le_rfl))).mono_height
        (OmegaPlus_le (le_max_left _ _)) (OmegaPlus_mem hH _)).weaken_seq hH.1
        (subset_cons_cons (List.subset_append_left _ _)) ?_
      exact paramsVal_cons_sub (params_tr_sub f φ) pR
    · refine ((ihn.mono_rank (hρ (Or.inr le_rfl))).mono_height
        (OmegaPlus_le (le_max_right _ _)) (OmegaPlus_mem hH _)).weaken_seq hH.1
        (subset_cons_cons (List.subset_append_right _ _)) ?_
      exact paramsVal_cons_sub (by rw [params_neg]; exact params_tr_sub f φ) pR

end Replay

/-! ### The axioms and their cut-away -/

section Main

/-- **Every axiom of `IDw A`** is derivable, cut-free, at a height `Ω_ω · 2 + m` (Freund,
proof of Theorem 6.5), dispatched to `EmbedHyps`. -/
theorem ax_derivable_of_mem (hyps : EmbedHyps A) (hA : PositiveP A)
    {θ : Sentence LXJ} (h : θ ∈ IDw A) : AxDerivable A θ := by
  rcases (mem_IDw A).mp h with rfl | h | ⟨F, rfl⟩
  · exact hyps.closure_axiom hA
  · rcases h with h | h | h
    · exact hyps.eq_axiom h
    · exact hyps.paMinus_axiom h
    · exact hyps.induction_axiom h
  · exact hyps.indAx_axiom hA F

/-- A common height for finitely many axioms. -/
theorem axDerivable_list (Δ : List (Sentence LXJ)) (h : ∀ θ ∈ Δ, AxDerivable A θ) :
    ∃ N : ℕ, ∀ θ ∈ Δ, ∀ H : Set ThetaVNoteD → Set ThetaVNoteD, ThetaVNoteD.NiceS H →
      IDwDerivable A ThetaVNoteD.zero H (OmegaTwo + ThetaVNoteD.ofNat N)
        [(Rewriting.emb (embK θ) : Proposition LIinfW)] := by
  induction Δ with
  | nil => exact ⟨0, fun θ hθ => absurd hθ (by simp)⟩
  | cons θ Δ ih =>
    obtain ⟨m, hm⟩ := h θ List.mem_cons_self
    obtain ⟨N, hN⟩ := ih fun θ' hθ' => h θ' (List.mem_cons_of_mem _ hθ')
    refine ⟨max m N, fun θ' hθ' H hH => ?_⟩
    have hmono : ∀ k, k ≤ max m N → OmegaTwo + ThetaVNoteD.ofNat k ≤
        OmegaTwo + ThetaVNoteD.ofNat (max m N) := fun k hk =>
      ThetaVNoteD.add_le_add_left _ (ThetaVNoteD.ofNat_le_ofNat hk)
    rcases List.mem_cons.mp hθ' with rfl | hθ'
    · exact (hm H hH).mono_height (hmono m (le_max_left _ _)) (OmegaTwo_mem hH _ _)
    · exact (hN θ' hθ' H hH).mono_height (hmono N (le_max_right _ _)) (OmegaTwo_mem hH _ _)

/-- A common bound for the complexities of finitely many embedded axioms. -/
theorem cx_list (Δ : List (Sentence LXJ)) :
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
private theorem paramsVal_negEmb_sub {H : Set ThetaVNoteD → Set ThetaVNoteD}
    (Δ : List (Sentence LXJ)) :
    paramsVal (Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition LIinfW))) ⊆ H ∅ := by
  induction Δ with
  | nil => simp [paramsVal]
  | cons θ' Δ ih =>
    rw [List.map_cons, paramsVal_cons]
    refine Set.union_subset ?_ ih
    rw [params_neg, params_rew]
    exact params_embK_sub θ'

/-- **Cutting away the axioms**, one at a time (Freund, proof of Theorem 6.5): each cut is on
an embedded axiom of rank `≺ Ω_ω + m`, against its derivation at height `Ω_ω · 2 + N`. -/
theorem cut_axioms {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.NiceS H)
    {N m : ℕ} :
    ∀ (Δ : List (Sentence LXJ)),
      (∀ θ ∈ Δ, IDwDerivable A ThetaVNoteD.zero H (OmegaTwo + ThetaVNoteD.ofNat N)
        [(Rewriting.emb (embK θ) : Proposition LIinfW)]) →
      (∀ θ ∈ Δ, (embK θ).complexity + 1 ≤ m) →
      ∀ {h : ℕ} {Θ : Sequent LIinfW}, N ≤ h → paramsVal Θ ⊆ H ∅ →
        IDwDerivable A (OmegaPlus m) H (OmegaTwo + ThetaVNoteD.ofNat h)
          (Θ ++ Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition LIinfW))) →
        IDwDerivable A (OmegaPlus m) H
          (OmegaTwo + ThetaVNoteD.ofNat (h + Δ.length)) Θ
  | [], _, _, h, Θ, _, _, d => by simpa using d
  | θ :: Δ, hax, hcx, h, Θ, hNh, hΘ, d => by
    set φ : Proposition LIinfW := Rewriting.emb (embK θ) with hφ
    have pφ : Stage.val '' params φ ⊆ H ∅ := by rw [hφ, params_rew]; exact params_embK_sub θ
    have pRest : paramsVal (Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition LIinfW)))
        ⊆ H ∅ := paramsVal_negEmb_sub Δ
    have pΘR : paramsVal
        (Θ ++ Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition LIinfW))) ⊆ H ∅ := by
      rw [paramsVal_append]; exact Set.union_subset hΘ pRest
    have hL : IDwDerivable A (OmegaPlus m) H (OmegaTwo + ThetaVNoteD.ofNat h)
        (∼φ :: (Θ ++ Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition LIinfW)))) :=
      d.weaken_seq hH.1 (by
        intro x hx
        simp only [List.map_cons, List.mem_append, List.mem_cons] at hx ⊢
        tauto) (paramsVal_cons_sub (by rw [params_neg]; exact pφ) pΘR)
    have hR : IDwDerivable A (OmegaPlus m) H (OmegaTwo + ThetaVNoteD.ofNat h)
        (φ :: (Θ ++ Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition LIinfW)))) :=
      (((hax θ List.mem_cons_self).mono_rank (ThetaVNoteD.zero_le' _)).mono_height
        (ThetaVNoteD.add_le_add_left _ (ThetaVNoteD.ofNat_le_ofNat hNh))
        (OmegaTwo_mem hH _ _)).weaken_seq hH.1
        (List.cons_subset_cons _ (List.nil_subset _)) (paramsVal_cons_sub pφ pΘR)
    have hrk : rk φ < OmegaPlus m := by
      rw [hφ, rk_rew]
      exact lt_of_le_of_lt (rk_le_OmegaW_add_ofNat _) (OmegaPlus_lt (by
        have := hcx θ List.mem_cons_self; omega))
    have hcut : IDwDerivable A (OmegaPlus m) H
        (OmegaTwo + ThetaVNoteD.ofNat (h + 1))
        (Θ ++ Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition LIinfW))) :=
      .cut (OmegaTwo_mem hH _ _) pΘR hrk
        (ThetaVNoteD.add_lt_add_left _ (ThetaVNoteD.ofNat_lt_ofNat (Nat.lt_succ_self h))) hR hL
    have key := cut_axioms hH Δ (fun θ' hθ' => hax θ' (List.mem_cons_of_mem _ hθ'))
      (fun θ' hθ' => hcx θ' (List.mem_cons_of_mem _ hθ')) (Nat.le_succ_of_le hNh) hΘ hcut
    rwa [show h + 1 + Δ.length = h + (θ :: Δ).length by simp; omega] at key

/-- **Freund, Theorem 6.5 (Embedding).** If `IDw A ⊢ σ`, then there are `m, r ∈ ℕ`
such that `H ⊢^{Ω_ω·2+r}_{Ω_ω+m} embed σ` for every operator `H` nice. As in
`ID1.Embed`, this is stated with `X` read as empty (`embK`); for an `X`-free `σ`, `embK σ =
embed σ` (`embK_eq_embed`). -/
theorem embedding_theorem (hyps : EmbedHyps A) (hA : PositiveP A)
    {σ : Sentence LXJ} (h : IDw A ⊢ σ) :
    ∃ m r : ℕ, ∀ H : Set ThetaVNoteD → Set ThetaVNoteD, ThetaVNoteD.NiceS H →
      IDwDerivable A (OmegaPlus m) H (OmegaTwo + ThetaVNoteD.ofNat r)
        [(Rewriting.emb (embK σ) : Proposition LIinfW)] := by
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := Theory.Proof.provable_iff.mp h
  have hax : ∀ θ ∈ Δ, AxDerivable A θ := fun θ hθ => ax_derivable_of_mem hyps hA (hΔ θ hθ)
  obtain ⟨N, hN⟩ := axDerivable_list Δ hax
  obtain ⟨m0, hm0⟩ := cx_list Δ
  refine ⟨max (cutCx d) m0, max (hgt d) N + Δ.length, fun H hH => ?_⟩
  have r := replay hyps hH d (fun _ => 0)
  have e : ((σ : Proposition LXJ) :: ∼Sequent.embed Δ).map (tr (fun _ => 0)) =
      [(Rewriting.emb (embK σ) : Proposition LIinfW)] ++
        Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition LIinfW)) := by
    rw [List.map_cons, tr_emb, List.singleton_append, List.tilde_def, Sequent.embed,
      List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun θ _ => ?_
    simp only [Function.comp_apply, tr_neg, tr_emb]
  rw [e] at r
  refine cut_axioms hH Δ (fun θ hθ => hN θ hθ H hH)
    (fun θ hθ => le_trans (hm0 θ hθ) (le_max_right _ _)) (le_max_right _ _)
    (paramsVal_cons_sub (paramsVal_of_params_eq (by rw [params_rew]; exact params_embK σ)) (by simp)) ?_
  refine (r.mono_rank (OmegaPlus_le (le_max_left _ _))).mono_height ?_ (OmegaTwo_mem hH _ _)
  -- `Ω_ω + hgt d ≤ (Ω_ω + Ω_ω) + max (hgt d) N`: no left-monotonicity of `+` is needed (`add`
  -- is not commutative and no such lemma is proved for it), only right-monotonicity plus
  -- `le_add_left` (`b ≤ a + b`) after `add_assoc` regroups the right-hand side.
  show OmegaPlus (hgt d) ≤ OmegaTwo + ThetaVNoteD.ofNat (max (hgt d) N)
  rw [OmegaTwo, ThetaVNoteD.add_assoc]
  exact ThetaVNoteD.add_le_add_left _ (le_trans
    (ThetaVNoteD.ofNat_le_ofNat (le_max_left _ _)) (ThetaVNoteD.le_add_left _ _))

/-- **Theorem 6.5 for `X`-free sentences**,: `H ⊢^{Ω_ω·2+r}_{Ω_ω+m}
σ⁺` with `σ⁺ = embed σ` (`I_k ↦ I_k^{≺Ω_{k+1}}`). -/
theorem embedding_theorem_xfree (hyps : EmbedHyps A) (hA : PositiveP A)
    {σ : Sentence LXJ} (hσ : XFreeL σ) (h : IDw A ⊢ σ) :
    ∃ m r : ℕ, ∀ H : Set ThetaVNoteD → Set ThetaVNoteD, ThetaVNoteD.NiceS H →
      IDwDerivable A (OmegaPlus m) H (OmegaTwo + ThetaVNoteD.ofNat r)
        [embed (σ : Proposition LXJ)] := by
  obtain ⟨m, r, hmr⟩ := embedding_theorem hyps hA h
  refine ⟨m, r, fun H hH => ?_⟩
  have e : embed (σ : Proposition LXJ) = (Rewriting.emb (embK σ) : Proposition LIinfW) := by
    rw [embK_eq_embed hσ]; exact Semiformula.lMap_emb σ
  rw [e]; exact hmr H hH

end Main

end IDw

end OrdinalAnalysis

