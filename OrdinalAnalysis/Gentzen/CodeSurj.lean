/-
  Surjectivity of the notation coding onto the internally recognised codes, in `ℕ`.

  `NotationBridge.isNF_modelCode` says every external normal form is accepted by the
  arithmetized recogniser: `NF o → isNF (modelCode o)`.  This file proves the converse
  in the standard model — every number the *internal* recogniser accepts really is the
  code of a normal-form notation:

      isNF_surj : isNF (V := ℕ) n → ∃ o : NONote, nonoteCode o = n

  so that on `ℕ` the range of `nonoteCode` is exactly `{n | isNF n}`
  (`isNF_iff_exists_nonote`), and the coded ordering `precN` of `PrecStandard`
  never leaves that range (`precN_dom`).

  Two remarks on why this is cheap here.

  * The characterisation the induction needs is already isolated.  The
    `isNFb` is a course-of-values table, but `InternalONote.isNF_ocOadd`
    (InternalONote.lean:689) collapses one table step into

        isNF (ocOadd ec n rc) ↔ n ≠ 0 ∧ isNF ec ∧ isNF rc ∧ (rc = 0 ∨ icmp (ocExp rc) ec = 0)

    and `InternalONote.ocOadd_destruct` (:708) says every positive code *is* an
    `ocOadd`.  With `ocExp_lt_of_pos` / `ocTail_lt_of_pos` as the measure, strong
    induction on the code writes itself.

  * Nothing new is needed to rebuild the notation.  The fourth conjunct is exactly
    `ONote.TopBelow` read through the bridge: `icmp_modelCode_eq_zero_iff` turns the
    internal `icmp … = 0` into `ONote.cmp … = Ordering.lt`, which is the definition of
    `TopBelow`, and `Code.lean`'s `nf_oadd_iff` assembles `ONote.NF` from it.  The code
    equation is then `modelCode_oadd` read at `V := ℕ`, where `modelCode = code`.

  This is the fact the ε₀ lower bound was designed *around* — the parameter-free
  predicate `∀ o, code o = n → o < β` was chosen precisely so that surjectivity of
  `code` onto the internal `isNF` codes would not be needed for the ε₀ lower bound.
  It is proved here because the ε₁ pipeline (§24.6) parameterises the boundedness
  machinery over a coded ordering, and a decoding step is the natural way to state
  that the coded ordering and the notation ordering are the *same* order and not
  merely an embedding.
-/
import OrdinalAnalysis.Gentzen.PrecStandard
import OrdinalAnalysis.Gentzen.Code

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.CodeSurj

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.NotationBridge
open OrdinalAnalysis.Gentzen.PrecStandard

/-! ### The model code in `ℕ` -/

/-- In the standard model the model code of an external notation is literally its
natural-number code.  (`PrecStandard.nonoteModelCode_nat` is this for normal forms;
the induction below meets arbitrary `ONote`s.) -/
@[simp] theorem modelCode_nat (o : ONote) : modelCode (V := ℕ) o = code o := by
  simp [modelCode]

/-! ### The decoding induction -/

set_option maxHeartbeats 2000000 in
/-- **Every internally recognised code is the code of a notation.**  Strong induction
on the code: `0` decodes to `0`, and a positive code is `ocOadd (ocExp n) (ocCoeff n)
(ocTail n)` by `ocOadd_destruct`, whose exponent and tail are smaller, so the induction
hypothesis supplies notations for them; `isNF_ocOadd` provides the four side conditions,
of which the coefficient one makes the `ℕ+` and the tail one becomes `ONote.TopBelow`
through `icmp_modelCode_eq_zero_iff`. -/
theorem isNF_surj (n : ℕ) (h : InternalONote.isNF (V := ℕ) n) :
    ∃ o : NONote, nonoteCode o = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hne
    · exact ⟨0, rfl⟩
    · have hpos : 0 < n := Nat.pos_of_ne_zero hne
      have hdes : ocOadd (ocExp (V := ℕ) n) (ocCoeff (V := ℕ) n) (ocTail (V := ℕ) n) = n :=
        ocOadd_destruct hne
      have hnf : InternalONote.isNF (V := ℕ)
          (ocOadd (ocExp (V := ℕ) n) (ocCoeff (V := ℕ) n) (ocTail (V := ℕ) n)) := by
        rw [hdes]; exact h
      rw [isNF_ocOadd] at hnf
      obtain ⟨hm, hexpNF, htailNF, htop⟩ := hnf
      obtain ⟨e, he⟩ := ih _ (ocExp_lt_of_pos hpos) hexpNF
      obtain ⟨r, hr⟩ := ih _ (ocTail_lt_of_pos hpos) htailNF
      obtain ⟨e, henf⟩ := e
      obtain ⟨r, hrnf⟩ := r
      have he' : code e = ocExp (V := ℕ) n := he
      have hr' : code r = ocTail (V := ℕ) n := hr
      -- the coefficient is positive, so it names an element of `ℕ+`.  It is packaged
      -- opaquely: writing `⟨_, _⟩ : ℕ+` inline makes the goal mention the *subtype*
      -- `{n // 0 < n}`, and `rw` then refuses the resulting non-type-correct motive.
      have hmpos : 0 < ocCoeff (V := ℕ) n := Nat.pos_of_ne_zero hm
      obtain ⟨c, hcv⟩ : ∃ c : ℕ+, (c : ℕ) = ocCoeff (V := ℕ) n := ⟨⟨_, hmpos⟩, rfl⟩
      -- the tail condition is `ONote.TopBelow`
      have htb : ONote.TopBelow e r := by
        cases r with
        | zero => trivial
        | oadd er nr rr =>
            have hrne : ocTail (V := ℕ) n ≠ 0 := by
              rw [← hr']; simp
            have hlt : icmp (V := ℕ) (ocExp (V := ℕ) (ocTail (V := ℕ) n))
                (ocExp (V := ℕ) n) = 0 := htop.resolve_left hrne
            rw [← he', ← hr'] at hlt
            have hexp : ocExp (V := ℕ) (code (ONote.oadd er nr rr)) = code er := by
              rw [← modelCode_nat, modelCode_oadd, ocExp_ocOadd, modelCode_nat]
            rw [hexp, ← modelCode_nat er, ← modelCode_nat e,
              icmp_modelCode_eq_zero_iff] at hlt
            exact hlt
      have hnfo : ONote.NF (ONote.oadd e c r) := nf_oadd_iff.mpr ⟨henf, hrnf, htb⟩
      -- the code equation is `modelCode_oadd` read at `V := ℕ`
      have hmc : code (ONote.oadd e c r) = ocOadd (code e) (ocCoeff (V := ℕ) n) (code r) := by
        -- `natCast_nat`, not `Nat.cast_id`: the `NatCast ℕ` here is the one Foundation
        -- derives from `ORingStructure ℕ`, which is not syntactically `instNatCastNat`.
        simpa only [modelCode_nat, natCast_nat, hcv] using modelCode_oadd (V := ℕ) e r c
      refine ⟨⟨ONote.oadd e c r, hnfo⟩, ?_⟩
      show code (ONote.oadd e c r) = n
      rw [hmc, he', hr']
      exact hdes

/-- On `ℕ`, the range of `nonoteCode` is exactly the set of codes the internal
recogniser accepts: `isNF_modelCode` gives one direction, `isNF_surj` the other. -/
theorem isNF_iff_exists_nonote (n : ℕ) :
    InternalONote.isNF (V := ℕ) n ↔ ∃ o : NONote, nonoteCode o = n := by
  refine ⟨isNF_surj n, ?_⟩
  rintro ⟨o, rfl⟩
  have := isNF_nonoteModelCode (V := ℕ) o
  rwa [nonoteModelCode_nat] at this

/-! ### The coded ordering has notations on both sides -/

/-- **The coded ordering never leaves the notations.**  `precN k n` unfolds to
`isNF k ∧ isNF n ∧ icmp k n = 0` (`PrecStandard.precN_iff`), and `isNF_surj` decodes
each side. -/
theorem precN_dom {k n : ℕ} (h : precN k n) :
    (∃ o : NONote, nonoteCode o = k) ∧ (∃ o : NONote, nonoteCode o = n) := by
  rw [precN_iff] at h
  exact ⟨isNF_surj k h.1, isNF_surj n h.2.1⟩

/-- The decoded witnesses of `precN_dom` are ordered as the notations are: the two
notations `precN` decodes to satisfy `a < b`.  (`PrecStandard.precN_code_iff` is the
same fact read from the other side.) -/
theorem precN_exists_lt {k n : ℕ} (h : precN k n) :
    ∃ a b : NONote, nonoteCode a = k ∧ nonoteCode b = n ∧ a < b := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := precN_dom h
  refine ⟨a, b, ha, hb, ?_⟩
  exact (precN_code_iff a b).mp (by rw [ha, hb]; exact h)

end OrdinalAnalysis.Gentzen.CodeSurj
