/-
  The internal arithmetic of the coded ϑ-notation on standard codes.

  In every model `V` of `IΣ₁` the functions of `Arith` compute, on the standard codes
  `mc t`, the list operations and the arithmetic of `Ordinal/Theta/Arith.lean`:

  * `itoL_mc`, `iofL_mc`: exponent lists (`toList`, `ofList`);
  * `imerge_mc`, `ifilt_mc`, `iapp_mc`, `iaddL_mc`, `imapOP_mc`: merge, filter, append,
    `addL`, and the map of `onePlus`;
  * `iadd_mc`, `inadd_mc`, `iomegaPow_mc`, `iomegaMul_mc`, `inum_mc`, `ione_mc`,
    `isucc_mc`: the ordinal sum, the natural sum, `ω^·`, `ω · ·`, the numerals, `1` and the
    successor of `ThetaNote`.
-/
import OrdinalAnalysis.ID1.Internal.Arith
import OrdinalAnalysis.Ordinal.Theta.Arith

set_option autoImplicit false

namespace OrdinalAnalysis.ID1.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.ThetaTerm

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Shapes of standard codes -/

lemma kind_mc_prin_iff (t : ThetaTerm) :
    (kind (mc (V := V) t) = 1 ∨ kind (mc (V := V) t) = 2) ↔ IsPrin t := by
  cases t with
  | Omega => simp
  | theta a => simp
  | sum xs => cases xs <;> simp

lemma sumK_mc_sum (xs : List ThetaTerm) : sumK (mc (V := V) (.sum xs)) = 1 := by
  cases xs <;> simp

/-! ### Exponent lists -/

theorem itoL_mc (t : ThetaTerm) : itoL (mc (V := V) t) = mc (.sum (toList t)) := by
  cases t with
  | Omega => simp
  | theta a => simp
  | sum xs => cases xs <;> simp

theorem iofL_mc (xs : List ThetaTerm) : iofL (mc (V := V) (.sum xs)) = mc (ofList xs) := by
  match xs with
  | [] => simp
  | [x] =>
    by_cases h : IsPrin x
    · rw [ofList_singleton_prin h, mc_cons, mc_nil,
        iofL_single_prin ((kind_mc_prin_iff x).mpr h)]
    · rw [ofList_singleton_not_prin h, mc_cons, mc_nil,
        iofL_single_of_not_prin (fun h' => h ((kind_mc_prin_iff x).mp h'))]
  | x :: y :: ys =>
    rw [mc_cons, iofL_of_tl_ne_zero _ (by simp), ← mc_cons]
    rfl

/-! ### List operations -/

lemma ige_mc_iff (x y : ThetaTerm) : ige (mc (V := V) x) (mc y) = 1 ↔ geb x y = true := by
  rw [ige_eq_one, iltb_mc, mc_inj]
  simp [geb, le_def]

theorem imerge_mc : ∀ xs ys : List ThetaTerm,
    imerge (mc (V := V) (.sum xs)) (mc (.sum ys)) = mc (.sum (mergeL xs ys))
  | [], ys => by simp
  | x :: xs, [] => by
    rw [mergeL_nil_right, mc_nil, imerge_zero_right (sumK_mc_sum _)]
  | x :: xs, y :: ys => by
    rw [mc_cons, mc_cons, imerge_cons_cons]
    by_cases h : geb x y = true
    · rw [if_pos ((ige_mc_iff x y).mpr h), ← mc_cons, imerge_mc xs (y :: ys), ← mc_cons]
      unfold mergeL
      rw [List.cons_merge_cons_pos geb xs ys h]
    · rw [if_neg (fun h' => h ((ige_mc_iff x y).mp h')), ← mc_cons, imerge_mc (x :: xs) ys,
        ← mc_cons]
      unfold mergeL
      rw [List.cons_merge_cons_neg geb xs ys h]
termination_by xs ys => xs.length + ys.length

theorem ifilt_mc (y : ThetaTerm) : ∀ xs : List ThetaTerm,
    ifilt (mc (V := V) (.sum xs)) (mc y) = mc (.sum (xs.filter (fun x => geb x y)))
  | [] => by simp
  | x :: xs => by
    rw [mc_cons, ifilt_cons, List.filter_cons]
    by_cases h : geb x y = true
    · rw [if_pos ((ige_mc_iff x y).mpr h), if_pos h, ifilt_mc y xs, mc_cons]
    · rw [if_neg (fun h' => h ((ige_mc_iff x y).mp h')), if_neg h, ifilt_mc y xs]

theorem iapp_mc (ys : List ThetaTerm) : ∀ xs : List ThetaTerm,
    iapp (mc (V := V) (.sum xs)) (mc (.sum ys)) = mc (.sum (xs ++ ys))
  | [] => by simp
  | x :: xs => by rw [mc_cons, iapp_cons, iapp_mc ys xs, List.cons_append, mc_cons]

theorem iaddL_mc (xs ys : List ThetaTerm) :
    iaddL (mc (V := V) (.sum xs)) (mc (.sum ys)) = mc (.sum (addL xs ys)) := by
  cases ys with
  | nil => simp
  | cons y ys =>
    rw [mc_cons, iaddL_cons, ifilt_mc, ← mc_cons, iapp_mc, addL_cons]

theorem imapOP_mc_aux (hop : ∀ e : ThetaTerm, ionePlus (mc (V := V) e) = mc (onePlus e)) :
    ∀ xs : List ThetaTerm, imapOP (mc (V := V) (.sum xs)) = mc (.sum (xs.map onePlus))
  | [] => by simp
  | x :: xs => by
    rw [mc_cons, imapOP_cons, imapOP_mc_aux hop xs, hop x, List.map_cons, mc_cons]

/-! ### The arithmetic of terms -/

lemma ione_eq_mc : (ione : V) = mc (.sum [.sum []]) := by simp [ione]

theorem iadd_mc_term (a b : ThetaTerm) :
    iadd (mc (V := V) a) (mc b) = mc (ofList (addL (toList a) (toList b))) := by
  rw [iadd, itoL_mc, itoL_mc, iaddL_mc, iofL_mc]

theorem inadd_mc_term (a b : ThetaTerm) :
    inadd (mc (V := V) a) (mc b) = mc (ofList (mergeL (toList a) (toList b))) := by
  rw [inadd, itoL_mc, itoL_mc, imerge_mc, iofL_mc]

theorem iomegaPow_mc_term (a : ThetaTerm) : iomegaPow (mc (V := V) a) = mc (ofList [a]) := by
  rw [iomegaPow, ← iofL_mc, mc_cons, mc_nil]

theorem ionePlus_mc (e : ThetaTerm) : ionePlus (mc (V := V) e) = mc (onePlus e) := by
  rw [ionePlus, ione_eq_mc, itoL_mc, iaddL_mc, iofL_mc, onePlus]

theorem imapOP_mc (xs : List ThetaTerm) :
    imapOP (mc (V := V) (.sum xs)) = mc (.sum (xs.map onePlus)) :=
  imapOP_mc_aux ionePlus_mc xs

theorem iomegaMul_mc_term (a : ThetaTerm) :
    iomegaMul (mc (V := V) a) = mc (ofList ((toList a).map onePlus)) := by
  rw [iomegaMul, itoL_mc, imapOP_mc, iofL_mc]

/-! ### The arithmetic of notations -/

/-- **The ordinal sum on standard codes.** -/
theorem iadd_mc (a b : ThetaNote) : iadd (mc (V := V) a.1) (mc b.1) = mc (a + b).1 :=
  iadd_mc_term a.1 b.1

/-- **The natural sum on standard codes.** -/
theorem inadd_mc (a b : ThetaNote) :
    inadd (mc (V := V) a.1) (mc b.1) = mc (ThetaNote.nadd a b).1 :=
  inadd_mc_term a.1 b.1

/-- **`ω^·` on standard codes.** -/
theorem iomegaPow_mc (a : ThetaNote) :
    iomegaPow (mc (V := V) a.1) = mc (ThetaNote.omegaPow a).1 :=
  iomegaPow_mc_term a.1

/-- **`ω · ·` on standard codes.** -/
theorem iomegaMul_mc (a : ThetaNote) :
    iomegaMul (mc (V := V) a.1) = mc (ThetaNote.omegaMul a).1 :=
  iomegaMul_mc_term a.1

theorem ione_mc : (ione : V) = mc ThetaNote.one.1 := by
  rw [ione_eq_mc]; rfl

/-- **The numerals on standard codes.** -/
theorem inum_mc (n : ℕ) : inum (n : V) = mc (ThetaNote.ofNat n).1 := by
  have hof : ∀ m : ℕ, (ThetaNote.ofNat m).1 = .sum (List.replicate m (.sum [])) := by
    intro m
    show ofList (List.replicate m (.sum [])) = _
    match m with
    | 0 => rfl
    | 1 => exact ofList_singleton_not_prin (by simp)
    | _ + 2 => rfl
  rw [hof]
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, inum_succ, ih, List.replicate_succ, mc_cons, mc_nil]

/-- **The successor on standard codes.** -/
theorem isucc_mc (a : ThetaNote) : isucc (mc (V := V) a.1) = mc (ThetaNote.succ a).1 := by
  rw [isucc, ione_mc, inadd_mc]; rfl

end OrdinalAnalysis.ID1.Internal
