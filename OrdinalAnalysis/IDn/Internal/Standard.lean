/-
  The coding of the multi-level ϑ-notation in the standard model, generalizing
  `ID1/Internal/Standard.lean`.

  Only the order-free predicates of `Codes.lean` are bridged here (`isTermb`, `ilen`, `iinE`,
  `iinG`): in `ℕ` the term recogniser accepts exactly the codes of terms, so the arithmetic
  formulas mean what they say.  The order (`iltb`), normal-form (`isNFb`) and domain (`isDom`)
  predicates are not built in `Codes.lean` (see its module docstring), so there is nothing to
  bridge for them here.
-/
import OrdinalAnalysis.IDn.Internal.Codes

set_option autoImplicit false

namespace OrdinalAnalysis.IDn.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.ThetaWTerm
open OrdinalAnalysis.ID1.Internal (band_eq_one bor_eq_one beq_eq_one)

/-! ## Codes as numbers -/

theorem code_Omega' (k : ℕ) : code (.Omega k) = tcOmega (V := ℕ) k := by
  have h := mc_Omega (V := ℕ) k
  simp only [mc_nat] at h
  simpa using h

theorem code_theta' (k : ℕ) (a : ThetaWTerm) :
    code (.theta k a) = tcTheta (V := ℕ) k (code a) := by
  have h := mc_theta (V := ℕ) k a
  simp only [mc_nat] at h
  simpa using h

theorem code_cons' (x : ThetaWTerm) (xs : List ThetaWTerm) :
    code (.sum (x :: xs)) = tcCons (V := ℕ) (code x) (code (.sum xs)) := by
  have h := mc_cons (V := ℕ) x xs
  simp only [mc_nat] at h
  exact h

/-- **Every number the term recogniser accepts is the code of a term.** -/
theorem isTerm_surj (n : ℕ) (h : isTerm n) : ∃ t : ThetaWTerm, code t = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    unfold isTerm at h
    rcases kind_cases n with hk | hk | hk | hk | hk
    · exact ⟨.sum [], by rw [code_nil, (kind_eq_zero_iff.mp hk)]⟩
    · exact ⟨.Omega (tcOmegaLev n), by rw [code_Omega', ← eq_tcOmega_of_kind hk]⟩
    · rw [eq_tcTheta_of_kind hk, isTermb_tcTheta] at h
      have hn0 : n ≠ 0 := fun e => by simp [e] at hk
      obtain ⟨a, ha⟩ := ih _ (tcThetaArg_lt hn0) h
      exact ⟨.theta (tcLev n) a, by rw [code_theta', ha, ← eq_tcTheta_of_kind hk]⟩
    · rw [eq_tcCons_of_kind hk, isTermb_tcCons, band_eq_one, band_eq_one] at h
      obtain ⟨h1, h2, h3⟩ := h
      have hn0 : n ≠ 0 := fun e => by simp [e] at hk
      obtain ⟨x, hx⟩ := ih _ (tcHd_lt hn0) h1
      obtain ⟨u, hu⟩ := ih _ (tcTl_lt hn0) h2
      cases u with
      | Omega k => rw [← hu, code_Omega'] at h3; simp [sumK] at h3
      | theta k b => rw [← hu, code_theta'] at h3; simp [sumK] at h3
      | sum ys =>
        exact ⟨.sum (x :: ys), by rw [code_cons', hx, hu, ← eq_tcCons_of_kind hk]⟩
    · rw [isTermb_kind_four hk] at h; simp at h

theorem isTerm_iff (n : ℕ) : isTerm n ↔ ∃ t : ThetaWTerm, code t = n := by
  refine ⟨isTerm_surj n, ?_⟩
  rintro ⟨t, rfl⟩
  simpa using isTerm_mc (V := ℕ) t

/-- **Coding inverts decoding on codes.** -/
theorem code_decode {n : ℕ} (h : isTerm n) : code (decode n) = n := by
  obtain ⟨t, rfl⟩ := isTerm_surj n h
  rw [decode_code]

/-! ## The formulas in `ℕ` -/

theorem eval_thTermDef_nat (n : ℕ) : thTermDef.val.Evalb ![n] ↔ ∃ t : ThetaWTerm, code t = n := by
  rw [eval_thTermDef, isTerm_iff]

theorem eval_thLenDef_code (m : ℕ) (t : ThetaWTerm) :
    thLenDef.val.Evalb ![m, code t] ↔ m = l t := by
  rw [eval_thLenDef]
  have h := ilen_mc (V := ℕ) t
  simp only [mc_nat] at h
  rw [h]
  simp

theorem eval_thInEDef_code (kk : ℕ) (g a : ThetaWTerm) :
    thInEDef.val.Evalb ![(kk : ℕ), code g, code a] ↔ g ∈ E kk a := by
  simpa using eval_thInEDef_mc (V := ℕ) kk g a

theorem eval_thGDef_code (kk : ℕ) (x a : ThetaWTerm) :
    thGDef.val.Evalb ![(kk : ℕ), code x, code a] ↔ x ∈ G kk a := by
  simpa using eval_thGDef_mc (V := ℕ) kk x a

/-! ### The slot check

The one way the level-tagged coding could silently go wrong is the level swapped somewhere in
`tcOmega`/`tcTheta`/`inEStep`/`inGStep` — e.g. `E_0` and `E_1` collapsing to the same clause, or
`iinE`/`iinG` reading the wrong coordinate of the position pair.  Checked here on concrete small
terms with genuinely different levels, per clause, exactly as `SlotCheck.lean` did once for `ID1`. -/

section SlotCheck

/-- A concrete term whose level-`0` and level-`1` coefficient sets differ: `ϑ₁(ϑ₀(Ω₃))`. -/
private def slotTerm : ThetaWTerm := theta 1 (theta 0 (Omega 2))

/-- **Codes tell levels apart**: swapping the two levels of `slotTerm` gives a different code —
a level-index swap in `tcTheta`'s pairing would make this provable only by luck. -/
theorem slotCheck_code_distinguishes_levels :
    code slotTerm ≠ code (theta 0 (theta 1 (Omega 2))) := by
  simp only [slotTerm, ne_eq, code_inj]
  decide

/-- **`E_0` and `E_1` genuinely differ on `slotTerm`**: the outer `ϑ₁` is invisible to `E_0`
(`0 ≤ 1` fails), so `E_0` drills to the inner `ϑ₀`-subterm; the outer `ϑ₁` is its own `E_1`. A
level swapped in the `≤`-test of `inEStep` would make one of these two facts fail. -/
theorem slotCheck_E0_ne_E1 : E 0 slotTerm ≠ E 1 slotTerm := by
  have h0 : E 0 slotTerm = [theta 0 (Omega 2)] := by
    simp [slotTerm, E_theta_of_lt (show (0:ℕ) < 1 by decide), E_theta_of_le (le_refl 0)]
  have h1 : E 1 slotTerm = [slotTerm] := by
    simp [slotTerm, E_theta_of_le (le_refl 1)]
  rw [h0, h1]
  simp [slotTerm]

/-- **`iinE` reproduces the two facts of `slotCheck_E0_ne_E1` on codes** (stated via `mc`, which
is `code` at `V := ℕ` by `mc_nat`). -/
theorem slotCheck_iinE_0 :
    iinE (V := ℕ) 0 (mc (V := ℕ) (theta 0 (Omega 2))) (mc slotTerm) = 1 :=
  (iinE_mc_mc (V := ℕ) 0 (theta 0 (Omega 2)) slotTerm).mpr
    (by simp [slotTerm, E_theta_of_lt (show (0:ℕ) < 1 by decide), E_theta_of_le (le_refl 0)])

theorem slotCheck_iinE_1 :
    iinE (V := ℕ) 1 (mc (V := ℕ) slotTerm) (mc slotTerm) = 1 :=
  (iinE_mc_mc (V := ℕ) 1 slotTerm slotTerm).mpr (by simp [slotTerm, E_theta_of_le (le_refl 1)])

theorem slotCheck_not_iinE_1 :
    iinE (V := ℕ) 1 (mc (V := ℕ) (theta 0 (Omega 2))) (mc slotTerm) ≠ 1 := by
  intro h
  have := (iinE_mc_mc (V := ℕ) 1 (theta 0 (Omega 2)) slotTerm).mp h
  simp [slotTerm, E_theta_of_le (le_refl 1)] at this

/-- **`iinG` (Wilken's `K*_{k+1}`) picks up the inner argument of a level-`1` collapse.** -/
theorem slotCheck_iinG_0 :
    iinG (V := ℕ) 0 (mc (V := ℕ) (theta 0 (Omega 2))) (mc slotTerm) = 1 :=
  (iinG_mc_mc (V := ℕ) 0 (theta 0 (Omega 2)) slotTerm).mpr
    (by simp [slotTerm, G_theta_of_lt (show (0:ℕ) < 1 by decide)])

theorem slotCheck_not_iinG_1 :
    iinG (V := ℕ) 1 (mc (V := ℕ) (theta 0 (Omega 2))) (mc slotTerm) ≠ 1 := by
  intro h
  have := (iinG_mc_mc (V := ℕ) 1 (theta 0 (Omega 2)) slotTerm).mp h
  simp [slotTerm, G_theta_of_le (le_refl 1)] at this

/-- **The term recogniser and decoding round-trip on a mixed concrete term.** -/
theorem slotCheck_isTerm_roundtrip :
    isTerm (code (sum [theta 1 (Omega 2), Omega 0])) ∧
      decode (code (sum [theta 1 (Omega 2), Omega 0])) = sum [theta 1 (Omega 2), Omega 0] := by
  refine ⟨?_, decode_code _⟩
  have h := isTerm_mc (V := ℕ) (sum [theta 1 (Omega 2), Omega 0])
  simpa only [mc_nat] using h

end SlotCheck

end OrdinalAnalysis.IDn.Internal
