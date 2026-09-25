/-
  Second helper for the multi-level lower bound (`IDn/LowerBound.lean`): the two theorems
  `IDn/LowerBoundAux.lean`'s own docstring already names as its "Contents" but does not yet
  contain (the Step 1 pass stopped after the swap infrastructure).
  Kept in a separate file since `LowerBoundAux.lean` itself is not to be
  edited again. Specialised throughout to `A := Upper.WForms F n` (the one family this file
  needs), unlike `LowerBoundAux.lean`'s generic `A`.

  Source: `OrdinalAnalysis.ID1.LowerBound.provable_fieldInI_of_ti` and
  `OrdinalAnalysis.ID1.StageSem.codeNote_mem_stageSet_acc`, generalised from one inductively
  defined predicate to `n` simultaneous ones, reading `X` as the *level-0* predicate `I_0`, and
  from the fixed bound `Ω` to an arbitrary bound `a` (the sharp headline is one instantiation
  `a := c n` of a generic-`a` lemma rather than a second sentence).

  Contents.

    `lvl0`                             the level-`0` index of `Fin n`, given `0 < n`
    `fieldInI0`                        **`∀x (x ≺ ⌜a⌝ → I_0 x)`**
    `noXN_DF`, `noXN_wForm`, `noXN_WForms`   the well-ordering forms mention no `X`
    `lMap_swapN_progX`, `lMap_swapN_ti`      `Prog(≺,X)` / `TI_a(≺,X)` under the swap `X ↦ I_0`
    `provable_fieldInI0_of_ti`         **`IDn n (WForms F n) ⊢ TI_a(≺,X)` gives `⊢ fieldInI0 a`**
    `codeAt0_mem_stageSetN_iff`        **the accessible part at level `0`, for `WForms F n`**
-/
import OrdinalAnalysis.IDn.LowerBoundAux
import OrdinalAnalysis.IDn.StageSemantics
import OrdinalAnalysis.IDn.UpperBound
import OrdinalAnalysis.IDn.Internal.OrderBridge
import Foundation.FirstOrder.Completeness

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.IDn.Upper
open OrdinalAnalysis.IDn.Internal (code)

variable {n : ℕ}

/-! ### The level-`0` index and the field sentence -/

/-- The level-`0` index of `Fin n`, given `0 < n`. -/
def lvl0 (hn : 0 < n) : Fin n := ⟨0, hn⟩

/-- **`∀x (x ≺ ⌜a⌝ → I_0 x)`**: the field below `a` lies in the accessible part `I_0`
(the IDn analogue of `ID1.LowerBound.fieldInI`). -/
def fieldInI0 (F : OrderFormulas) (n : ℕ) (hn : 0 < n) (a : ThetaWNoteD) : Sentence (LXIn n) :=
  ∀¹ (lm (belowC F a) 🡒 Iat (lvl0 hn) #0)

/-! ### The well-ordering forms mention no `X` -/

/-- `DF` (for the specific level map `ixFin hn` used by `WForms`) mentions no `X`. -/
theorem noXN_DF (F : OrderFormulas) (hn : 0 < n) :
    ∀ j : ℕ, NoXN (DF F (ixFin hn) j : Semisentence (LXIn n) 1)
  | 0 => noXN_lMap_toLXIN _
  | j + 1 => ⟨noXN_DF F hn j, (noXN_imp _ _).mpr ⟨noXN_lMap_toLXIN _, noXN_Iat _ _⟩⟩

/-- `wForm` (for the specific level map `ixFin hn` used by `WForms`) mentions no `X`. -/
theorem noXN_wForm (F : OrderFormulas) (hn : 0 < n) :
    ∀ k : ℕ, NoXN (wForm F (ixFin hn) k : Semisentence (LXIn n) 1)
  | 0 => (noXN_imp _ _).mpr ⟨noXN_lMap_toLXIN _, noXN_Iat _ _⟩
  | k + 1 =>
    ⟨noXN_DF F hn (k + 1), noXN_lMap_toLXIN _,
      (noXN_imp _ _).mpr ⟨⟨(noXN_rew _ _).mpr (noXN_DF F hn (k + 1)),
        noXN_lMap_toLXIN _⟩, noXN_Iat _ _⟩⟩

variable (F : OrderFormulas)

theorem noXN_WForms (k : Fin n) :
    NoXN (Rewriting.emb (WForms F n k) : Semiformula (LXIn n) ℕ 1) :=
  (noXN_rew _ _).mpr (noXN_wForm F k.pos k.val)

/-! ### `Prog(≺, X)` and `TI_a(≺, X)` under the swap `X ↦ I_0` -/

section Swap0

variable {hn : 0 < n}

theorem ixFin_zero (hn : 0 < n) : ixFin hn 0 = lvl0 hn := Fin.ext (Nat.zero_mod n)

theorem wForms_zero_eq (hn : 0 < n) :
    WForms F n (lvl0 hn) = wForm F (ixFin hn) 0 := rfl

/-- **`Prog(≺, X)` is mapped to the closure axiom of `I_0`** under `X ↦ I_0`. -/
theorem lMap_swapN_progX (hn : 0 < n) :
    Semiformula.lMap (swapXIN (lvl0 hn)) (progX F (Fin n)) =
      closureAxAt (lvl0 hn) (WForms F n (lvl0 hn)) := by
  rw [wForms_zero_eq F hn]
  show Semiformula.lMap (swapXIN (lvl0 hn))
      (∀¹ ((∀¹ (precL F (Fin n) 🡒 Xat #0)) 🡒 Xat #0)) =
    ∀¹ (wForm F (ixFin hn) 0 🡒 Iat (lvl0 hn) #0)
  unfold precL
  simp only [Semiformula.lMap_all, LogicalConnective.HomClass.map_imply, lMap_swapN_Xat,
    lMap_swap_of_noXN _ _ (noXN_lMap_toLXIN (OrderFormulas.precW F))]
  rfl

/-- **`TI_a(≺, X)` is mapped to `closure(I_0) → fieldInI0 a`** under `X ↦ I_0`. -/
theorem lMap_swapN_ti (hn : 0 < n) (a : ThetaWNoteD) :
    Semiformula.lMap (swapXIN (lvl0 hn)) (tiUptoSentence F (Fin n) a) =
      (closureAxAt (lvl0 hn) (WForms F n (lvl0 hn)) 🡒 fieldInI0 F n hn a) := by
  unfold tiUptoSentence fieldInI0
  rw [LogicalConnective.HomClass.map_imply, lMap_swapN_progX F hn, Semiformula.lMap_all,
    LogicalConnective.HomClass.map_imply, lMap_swapN_Xat,
    lMap_swap_of_noXN _ _ (noXN_lMap_toLXIN (belowC F a))]

end Swap0

/-! ### From `TI_a(≺, X)` to `fieldInI0 a` -/

section Provable

/-- A sentence provable in `IDn n A` is true in every structure satisfying its axioms. -/
theorem eval_of_provable_of_axiomsN {A : Fin n → Semisentence (LXIn n) 1} {M : Type}
    [Nonempty M] (s : Structure (LXIn n) M)
    (hM : ∀ σ ∈ IDn n A, Semiformula.Eval (s := s) ![] Empty.elim σ) {σ : Sentence (LXIn n)}
    (h : IDn n A ⊢ σ) : Semiformula.Eval (s := s) ![] Empty.elim σ := by
  let _ : Structure (LXIn n) M := s
  have hT : M↓[LXIn n] ⊧* IDn n A :=
    Semantics.modelsSet_iff.mpr fun τ hτ => models_iff.mpr (hM τ hτ)
  exact models_iff.mp (models_of_provable hT h)

/-- **Reading `X` as `I_0`**: if `IDn n (WForms F n)` proves `TI_a(≺, X)`, it proves that the
field below `a` lies in the accessible part `I_0` (the direct analogue of
`ID1.LowerBound.provable_fieldInI_of_ti`). -/
theorem provable_fieldInI0_of_ti (hn : 0 < n) {a : ThetaWNoteD}
    (h : IDn n (WForms F n) ⊢ tiUptoSentence F (Fin n) a) :
    IDn n (WForms F n) ⊢ fieldInI0 F n hn a := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq]
  intro M _ s hEq hM
  have hAx : ∀ σ ∈ IDn n (WForms F n), Semiformula.Eval (s := s) ![] Empty.elim σ :=
    fun σ hσ => models_iff.mp ((Semantics.modelsSet_iff.mp hM) hσ)
  have hEq' : ∀ a b : M, s.rel (Language.Eq.eq : (LXIn n).Rel 2) ![a, b] ↔ a = b :=
    fun a b => hEq.eq a b
  have hswap := eval_of_provable_of_axiomsN (s.lMap (swapXIN (lvl0 hn)))
    (fun σ hσ => eval_swap_of_mem_IDn (lvl0 hn) (noXN_WForms F) s hEq' hAx hσ) h
  rw [← Semiformula.eval_lMap, lMap_swapN_ti F hn, LogicalConnective.HomClass.map_imply] at hswap
  exact models_iff.mpr (hswap (hAx _ (closureAxAt_mem_ID (WForms F n) (lvl0 hn))))

end Provable

/-! ### The accessible part at level `0`, for `WForms F n` -/

section Acc

open StageSem

variable (hn : 0 < n) (P : ℕ → Prop)

theorem relI_stdIN {S : Fin n → Set ℕ} (j : Fin n) (x : ℕ) :
    relI (stdIN P S) j x ↔ x ∈ S j := Iff.rfl

/-- **The stages of the accessible part of level `0`, for `WForms orderFormulas n`** (the direct
analogue of `ID1.StageSem.codeNote_mem_stageSet_acc`): the code of a normal domain term `β`
enters the stage `a : StageAt 0` exactly when `β ≺ a`. Fixed to the concrete
`Upper.orderFormulas` (`IDn/InternalFacts.lean`), the instance `IDn/Internal/OrderBridge.lean`'s
order-bridge facts are stated for. -/
theorem codeAt0_mem_stageSetN_iff (a : StageAt (lvl0 hn).val) (β : ThetaWNoteD) :
    (code β.1 : ℕ) ∈ stageSetN P (WForms orderFormulas n) (⟨lvl0 hn, a⟩ : Stage n) ↔
      β < a.1 := by
  induction a using WellFoundedLT.induction generalizing β with
  | _ a ih =>
  rw [mem_stageSetN_iff P (WForms orderFormulas n) (wForms_levelBounded orderFormulas n (lvl0 hn))]
  have hzero : WForms orderFormulas n (lvl0 hn) = wForm orderFormulas (ixFin hn) 0 :=
    wForms_zero_eq orderFormulas hn
  have hunfold : ∀ (g : StageAt (lvl0 hn).val) (x : ℕ),
      x ∈ opA P (WForms orderFormulas n) (lvl0 hn)
          (stageEnvAt (stageSetN P (WForms orderFormulas n)) (lvl0 hn) g) ↔
        ∀ y, orderFormulas.fld y → orderFormulas.fld x → orderFormulas.lt y x →
          y ∈ stageSetN P (WForms orderFormulas n) (⟨lvl0 hn, g⟩ : Stage n) := by
    intro g x
    show Semiformula.Eval
      (s := stdIN P (stageEnvAt (stageSetN P (WForms orderFormulas n)) (lvl0 hn) g))
      ![x] Empty.elim (WForms orderFormulas n (lvl0 hn)) ↔ _
    rw [hzero, eval_wForm_zero orderFormulas (ixFin hn) (stdIN P _) (stdIN_lMap_toLXIN P _) x]
    refine forall_congr' fun y => forall_congr' fun _ => forall_congr' fun _ =>
      forall_congr' fun _ => ?_
    rw [ixFin_zero hn, relI_stdIN P (lvl0 hn)]
    show _ ↔ y ∈ stageEnvAt (stageSetN P (WForms orderFormulas n)) (lvl0 hn) g (lvl0 hn)
    rw [stageEnvAt, dif_pos rfl]
  constructor
  · rintro ⟨g, hga, hg⟩
    rw [hunfold] at hg
    by_contra hβa
    have hgβ : g.1 < β := lt_of_lt_of_le hga (not_lt.mp hβa)
    have hmem := hg (code g.1.1) (Internal.eval_fld_iff g.1.1 |>.mpr g.1.2)
      (Internal.eval_fld_iff β.1 |>.mpr β.2) ((Internal.eval_lt_iff_lt g.1.1 β.1).mpr hgβ)
    exact lt_irrefl g.1 ((ih g hga g.1).mp hmem)
  · intro hβa
    refine ⟨⟨β, le_trans (le_of_lt hβa) a.2⟩, hβa, ?_⟩
    rw [hunfold]
    intro y hy _hβfld hylt
    obtain ⟨t, ht⟩ := Internal.fld_surj y hy
    have hty : t.1 < β.1 := (Internal.eval_lt_iff_lt t.1 β.1).mp (by rw [ht]; exact hylt)
    have := (ih ⟨β, le_trans (le_of_lt hβa) a.2⟩ hβa t).mpr hty
    rwa [ht] at this

end Acc

end IDn

end OrdinalAnalysis
