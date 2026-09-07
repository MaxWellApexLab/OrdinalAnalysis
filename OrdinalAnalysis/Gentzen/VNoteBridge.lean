/-
  Reflection of the external Veblen notations into the internal HFS coding.

  This is the `Γ₀` analogue of `OrdinalAnalysis.Gentzen.NotationBridge`.  The external
  `VNote` recursion and the internal arithmetized recursion of `InternalVNote` use the same
  pairing layout, so the syntactic comparison `VNote.cmp` and the arithmetized `icmp₁` agree
  on codes — and, unlike the correctness statement `VNote.cmp_eq_cmp_repr`, that agreement
  needs **no** normality hypothesis: it is a pure statement about two recursions with the same
  shape.  Normality only enters when the comparison is read as an order of ordinals
  (`lt_iff_icmp₁_modelCode_eq_zero`) and in the normal-form transfer `isNF₁_modelCode`.

  The last section is the converse of the latter, in the standard model: every number the
  internal recogniser accepts really is the code of a `Gamma0Note` (`isNF₁_surj`), so on `ℕ`
  the range of `gamma0Code` is exactly `{n | isNF₁ n}`.  The one genuinely new ingredient
  there is `repr_lt_veblen_of_cmp`: the coded side condition `b ≺ φ_a(b)` has to be turned
  back into `repr b < veblen (repr a) (repr b)` *without* already knowing that `vadd a b 1 0`
  is a normal form — which is exactly what the syntactic fixed-point test of
  `VNote.repr_lt_veblen_of_test` / `VNote.veblen_repr_eq_of_test` is for.
-/
import OrdinalAnalysis.Gentzen.InternalVNote
import OrdinalAnalysis.Gentzen.NotationBridge
import OrdinalAnalysis.Ordinal.Veblen.Gamma0Note

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OrdinalAnalysis.Gentzen.VNoteBridge

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.InternalVNote
open OrdinalAnalysis.Gentzen.NotationBridge (orderingCode thenV_orderingCode cmpV_natCast)

/-! ## Codes of Veblen notations -/

/-- The primitive-recursive natural-number code of a Veblen notation.  It uses exactly the
layout of `InternalVNote.vcVadd`: `φ_a(b)·n + c ↦ ⟪⟪⟪a,b⟫,n⟫,c⟫ + 1`. -/
def vcode : VNote → ℕ
  | VNote.zero => 0
  | VNote.vadd a b n c =>
      Nat.pair (Nat.pair (Nat.pair (vcode a) (vcode b)) (n : ℕ)) (vcode c) + 1

@[simp] lemma vcode_zero : vcode 0 = 0 := rfl

@[simp] lemma vcode_vadd (a b : VNote) (n : ℕ+) (c : VNote) :
    vcode (VNote.vadd a b n c)
      = Nat.pair (Nat.pair (Nat.pair (vcode a) (vcode b)) (n : ℕ)) (vcode c) + 1 := rfl

/-- The standard numeral denoting an external Veblen code in an arithmetic model. -/
def vmodelCode {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (o : VNote) : V := (vcode o : V)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] lemma vmodelCode_zero : vmodelCode (V := V) 0 = 0 := by
  simp [vmodelCode]

@[simp] lemma numeral_vcode_eq_vmodelCode (o : VNote) :
    ORingStructure.numeral (vcode o) = vmodelCode (V := V) o := by
  simp [vmodelCode, numeral_eq_natCast]

@[simp] lemma vmodelCode_vadd (a b : VNote) (n : ℕ+) (c : VNote) :
    vmodelCode (V := V) (VNote.vadd a b n c) =
      vcVadd (vmodelCode (V := V) a) (vmodelCode (V := V) b) ((n : ℕ) : V)
        (vmodelCode (V := V) c) := by
  simp [vmodelCode, vcVadd, coe_pair_eq_pair_coe]

/-- The single Veblen term `φ_a(b)` is coded by `vcVadd … 1 0`, which is the code the internal
comparison feeds back into itself. -/
@[simp] lemma vmodelCode_vadd_one_zero (a b : VNote) :
    vmodelCode (V := V) (VNote.vadd a b 1 0) =
      vcVadd (vmodelCode (V := V) a) (vmodelCode (V := V) b) 1 0 := by
  rw [vmodelCode_vadd, vmodelCode_zero]
  simp

/-! ## `icmp₁` computes `VNote.cmp` -/

/-- The three-way dispatch `leadV` at an ordering code. -/
private lemma leadV_orderingCode (o : Ordering) (p q r : V) :
    leadV ((orderingCode o : ℕ) : V) p q r =
      match o with
      | Ordering.eq => p
      | Ordering.lt => q
      | Ordering.gt => r := by
  cases o
  · show leadV (((0 : ℕ)) : V) p q r = q
    rw [Nat.cast_zero, leadV_zero]
  · show leadV (((1 : ℕ)) : V) p q r = p
    rw [Nat.cast_one, leadV_one]
  · show leadV (((2 : ℕ)) : V) p q r = r
    rw [show (((2 : ℕ)) : V) = 2 by simp, leadV_two]

/-- **Exact agreement of the external Veblen comparator with the internal one.**

No normality hypothesis is needed: `VNote.cmp` and `icmp₁` are the same recursion, run on
notations and on codes respectively.  (The `n ≠ 0` side conditions of
`InternalVNote.icmp₁_vcVadd_vcVadd` are supplied for free by the `ℕ+` coefficients.) -/
theorem icmp₁_modelCode : ∀ a b : VNote,
    icmp₁ (vmodelCode (V := V) a) (vmodelCode (V := V) b) =
      (orderingCode (VNote.cmp a b) : V)
  | 0, 0 => by
      rw [vmodelCode_zero, icmp₁_zero_zero, VNote.cmp_zero_zero]
      simp [orderingCode]
  | 0, VNote.vadd a' b' n' c' => by
      rw [vmodelCode_zero, vmodelCode_vadd, icmp₁_zero_vcVadd, VNote.cmp_zero_vadd]
      simp [orderingCode]
  | VNote.vadd a b n c, 0 => by
      rw [vmodelCode_zero, vmodelCode_vadd, icmp₁_vcVadd_zero, VNote.cmp_vadd_zero]
      simp [orderingCode]
  | VNote.vadd a b n c, VNote.vadd a' b' n' c' => by
      have hn : ((n : ℕ) : V) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt n.2)
      have hn' : ((n' : ℕ) : V) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt n'.2)
      have hA := icmp₁_modelCode a a'
      have hB := icmp₁_modelCode b b'
      have hC := icmp₁_modelCode c c'
      have hBL := icmp₁_modelCode b (VNote.vadd a' b' 1 0)
      have hLB := icmp₁_modelCode (VNote.vadd a b 1 0) b'
      rw [vmodelCode_vadd_one_zero] at hBL hLB
      rw [vmodelCode_vadd, vmodelCode_vadd, icmp₁_vcVadd_vcVadd hn hn', VNote.cmp_vadd_vadd,
        hA, hB, hC, hBL, hLB, cmpV_natCast, leadV_orderingCode]
      cases VNote.cmp a a' <;> simp only [thenV_orderingCode]

termination_by a b => VNote.size a + VNote.size b
decreasing_by
  all_goals
    simp only [VNote.size_vadd, VNote.size_zero]
    omega

@[simp] theorem icmp₁_modelCode_eq_zero_iff (a b : VNote) :
    icmp₁ (vmodelCode (V := V) a) (vmodelCode (V := V) b) = 0 ↔
      VNote.cmp a b = Ordering.lt := by
  rw [icmp₁_modelCode]
  cases VNote.cmp a b <;> simp [orderingCode]

/-! ## Normal forms -/

/-- **Every external Veblen normal form is recognised by `isNF₁`** in every model of `IΣ₁`,
when inserted as its standard natural-number code. -/
theorem isNF₁_modelCode : ∀ o : VNote, VNote.NF o → isNF₁ (vmodelCode (V := V) o) := by
  intro o
  induction o with
  | zero => intro _; exact isNF₁_zero
  | vadd a b n c iha ihb ihc =>
      intro h
      have hnf1 : VNote.NF (VNote.vadd a b 1 0) :=
        VNote.NF.vadd_zero 1 h.fst h.snd h.snd_lt
      rw [vmodelCode_vadd, isNF₁_vcVadd]
      refine ⟨by exact_mod_cast (Nat.ne_of_gt n.2), iha h.fst, ihb h.snd, ihc h.tail, ?_, ?_⟩
      · rw [← vmodelCode_vadd_one_zero, icmp₁_modelCode_eq_zero_iff,
          ← VNote.repr_lt_iff h.snd hnf1]
        simpa using h.snd_lt
      · rw [← vmodelCode_vadd_one_zero, icmp₁_modelCode_eq_zero_iff,
          ← VNote.repr_lt_iff h.tail hnf1]
        simpa using h.tail_lt

/-- **On external normal forms, the ordinal order is precisely internal comparison code
zero.**  This is the `Γ₀` analogue of `NotationBridge.lt_iff_icmp_modelCode_eq_zero`, and the
statement the ε₁ boundedness pipeline consumes. -/
theorem lt_iff_icmp₁_modelCode_eq_zero {a b : VNote} (ha : VNote.NF a) (hb : VNote.NF b) :
    VNote.repr a < VNote.repr b ↔
      icmp₁ (vmodelCode (V := V) a) (vmodelCode (V := V) b) = 0 := by
  rw [icmp₁_modelCode_eq_zero_iff]
  exact VNote.repr_lt_iff ha hb

/-! ## The subtype `Gamma0Note` -/

/-- Natural-number code specialised to Veblen normal forms. -/
def gamma0Code (o : Gamma0Note) : ℕ := vcode o.1

/-- A normal Veblen code interpreted in an arithmetic model. -/
def gamma0ModelCode (o : Gamma0Note) : V := (gamma0Code o : V)

@[simp] lemma gamma0ModelCode_eq (o : Gamma0Note) :
    gamma0ModelCode (V := V) o = vmodelCode (V := V) o.1 := rfl

theorem isNF₁_gamma0ModelCode (o : Gamma0Note) : isNF₁ (gamma0ModelCode (V := V) o) := by
  rw [gamma0ModelCode_eq]
  exact isNF₁_modelCode o.1 o.2

theorem gamma0_lt_iff_icmp₁_eq_zero (a b : Gamma0Note) :
    a < b ↔ icmp₁ (gamma0ModelCode (V := V) a) (gamma0ModelCode (V := V) b) = 0 := by
  rw [gamma0ModelCode_eq, gamma0ModelCode_eq]
  exact lt_iff_icmp₁_modelCode_eq_zero a.2 b.2

/-! ### Injectivity of the coding -/

theorem vcode_injective : Function.Injective vcode := by
  intro x
  induction x with
  | zero =>
      intro y h
      cases y with
      | zero => rfl
      | vadd a' b' n' c' => simp only [VNote.zero_def, vcode_zero, vcode_vadd] at h; omega
  | vadd a b n c iha ihb ihc =>
      intro y h
      cases y with
      | zero => simp only [VNote.zero_def, vcode_zero, vcode_vadd] at h; omega
      | vadd a' b' n' c' =>
          simp only [vcode_vadd] at h
          have h1 : Nat.pair (Nat.pair (Nat.pair (vcode a) (vcode b)) (n : ℕ)) (vcode c)
              = Nat.pair (Nat.pair (Nat.pair (vcode a') (vcode b')) (n' : ℕ)) (vcode c') := by
            omega
          rw [Nat.pair_eq_pair, Nat.pair_eq_pair, Nat.pair_eq_pair] at h1
          obtain ⟨⟨⟨ha, hb⟩, hn⟩, hc⟩ := h1
          rw [iha ha, ihb hb, ihc hc, PNat.coe_injective hn]

theorem gamma0Code_injective : Function.Injective gamma0Code := fun _ _ h =>
  Subtype.ext (vcode_injective h)

@[simp] theorem gamma0Code_inj {a b : Gamma0Note} : gamma0Code a = gamma0Code b ↔ a = b :=
  gamma0Code_injective.eq_iff

/-! ## Surjectivity onto the internally recognised codes, in `ℕ`

`isNF₁_modelCode` says every external normal form is accepted by the arithmetized recogniser.
Here is the converse in the standard model.  Compare `Gentzen.CodeSurj.isNF_surj`; the extra
work relative to the `ε₀` case is `repr_lt_veblen_of_cmp` below. -/

/-- In the standard model the model code of a Veblen notation is literally its code. -/
@[simp] theorem vmodelCode_nat (o : VNote) : vmodelCode (V := ℕ) o = vcode o := by
  simp [vmodelCode]

/-- The same for the normal-form subtype. -/
@[simp] theorem gamma0ModelCode_nat (o : Gamma0Note) :
    gamma0ModelCode (V := ℕ) o = gamma0Code o := by
  simp [gamma0ModelCode]

/-- **Reading the coded fixed-point condition back on notations.**

The internal normal form records `b ≺ φ_a(b)` as `icmp₁ (code b) (vcVadd a b 1 0) = 0`, i.e.
as `VNote.cmp b (vadd a b 1 0) = lt`.  Turning that into `repr b < veblen (repr a) (repr b)`
cannot go through `VNote.cmp_eq_cmp_repr`, which would need `NF (vadd a b 1 0)` — precisely
what is being established.  Instead one runs the *syntactic* fixed-point test of
`Gamma0Note.lean`: if `b` passes it then `cmp b (vadd a b 1 0)` is `eq`, not `lt`; if `b`
fails it then `VNote.repr_lt_veblen_of_test` gives the inequality outright. -/
theorem repr_lt_veblen_of_cmp {a b : VNote} (ha : VNote.NF a) (hb : VNote.NF b)
    (h : VNote.cmp b (VNote.vadd a b 1 0) = Ordering.lt) :
    VNote.repr b < Ordinal.veblen (VNote.repr a) (VNote.repr b) := by
  cases b with
  | zero =>
      -- `VNote.repr 0 = 0` definitionally, so this is just `0 < φ_a(0)`
      exact Ordinal.veblen_pos
  | vadd b₁ b₂ m d =>
      by_cases htest : m = 1 ∧ d = 0 ∧ VNote.cmp a b₁ = Ordering.lt
      · exfalso
        obtain ⟨hm, hd, hcmp⟩ := htest
        subst hm
        subst hd
        have hb₁ : VNote.NF b₁ := hb.fst
        have hba : VNote.cmp b₁ a = Ordering.gt := by
          have h1 : VNote.repr a < VNote.repr b₁ := (VNote.repr_lt_iff ha hb₁).2 hcmp
          rw [VNote.cmp_eq_cmp_repr b₁ a hb₁ ha]
          exact h1.cmp_eq_gt
        rw [VNote.cmp_vadd_vadd] at h
        simp only [hba, VNote.cmp_eq_eq_of_eq hb hb rfl] at h
        simp at h
      · exact VNote.repr_lt_veblen_of_test ha hb htest

/-- **Every internally recognised code is the code of a Veblen normal form.**

Strong induction on the code: `0` decodes to `0`, and a positive code is
`vcVadd (vcFst n) (vcSnd n) (vcCoeff n) (vcTail n)` by `vcVadd_destruct`, whose three
subcodes are smaller, so the induction hypothesis supplies notations for them.
`isNF₁_vcVadd` provides the five side conditions: the coefficient one makes the `ℕ+`, and the
two comparison ones become the normal-form side conditions of `VNote.NF` through
`icmp₁_modelCode_eq_zero_iff` — the first via `repr_lt_veblen_of_cmp`, and then the second
via `VNote.repr_lt_iff`, which by then may use the normality of `vadd a b 1 0` established by
the first. -/
theorem isNF₁_surj (n : ℕ) (h : isNF₁ (V := ℕ) n) : ∃ o : Gamma0Note, gamma0Code o = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hne
    · exact ⟨0, rfl⟩
    · have hpos : 0 < n := Nat.pos_of_ne_zero hne
      have hdes : vcVadd (V := ℕ) (vcFst (V := ℕ) n) (vcSnd (V := ℕ) n) (vcCoeff (V := ℕ) n)
          (vcTail (V := ℕ) n) = n := vcVadd_destruct hne
      obtain ⟨hm, hA, hB, hC, hfix, htail⟩ := isNF₁_destruct hne h
      obtain ⟨oa, hae⟩ := ih _ (vcFst_lt_of_pos hpos) hA
      obtain ⟨ob, hbe⟩ := ih _ (vcSnd_lt_of_pos hpos) hB
      obtain ⟨oc, hce⟩ := ih _ (vcTail_lt_of_pos hpos) hC
      obtain ⟨a, ha⟩ := oa
      obtain ⟨b, hb⟩ := ob
      obtain ⟨c, hc⟩ := oc
      have hae' : vcode a = vcFst (V := ℕ) n := hae
      have hbe' : vcode b = vcSnd (V := ℕ) n := hbe
      have hce' : vcode c = vcTail (V := ℕ) n := hce
      -- the coefficient is positive, so it names an element of `ℕ+`
      have hmpos : 0 < vcCoeff (V := ℕ) n := Nat.pos_of_ne_zero hm
      obtain ⟨k, hkv⟩ : ∃ k : ℕ+, (k : ℕ) = vcCoeff (V := ℕ) n := ⟨⟨_, hmpos⟩, rfl⟩
      -- the coded leading term is the model code of `vadd a b 1 0`
      have hlead : vcLead (V := ℕ) n = vmodelCode (V := ℕ) (VNote.vadd a b 1 0) := by
        rw [vmodelCode_vadd_one_zero, vmodelCode_nat, vmodelCode_nat, hae', hbe']
        rfl
      -- side condition 1: `b` is not a fixed point of `φ_a`
      have hsnd : VNote.repr b < Ordinal.veblen (VNote.repr a) (VNote.repr b) := by
        refine repr_lt_veblen_of_cmp ha hb ?_
        rw [← icmp₁_modelCode_eq_zero_iff (V := ℕ), vmodelCode_nat, hbe', ← hlead]
        exact hfix
      have hnf1 : VNote.NF (VNote.vadd a b 1 0) := VNote.NF.vadd_zero 1 ha hb hsnd
      -- side condition 2: the tail is below the leading term
      have htl : VNote.repr c < Ordinal.veblen (VNote.repr a) (VNote.repr b) := by
        have hlt : VNote.cmp c (VNote.vadd a b 1 0) = Ordering.lt := by
          rw [← icmp₁_modelCode_eq_zero_iff (V := ℕ), vmodelCode_nat, hce', ← hlead]
          exact htail
        have hh := (VNote.repr_lt_iff hc hnf1).2 hlt
        simpa using hh
      have hnfo : VNote.NF (VNote.vadd a b k c) := VNote.NF.vadd ha hb hc hsnd htl
      -- the code equation is `vmodelCode_vadd` read at `V := ℕ`
      have hmc : vcode (VNote.vadd a b k c)
          = vcVadd (V := ℕ) (vcode a) (vcode b) (vcCoeff (V := ℕ) n) (vcode c) := by
        simpa only [vmodelCode_nat, natCast_nat, hkv] using vmodelCode_vadd (V := ℕ) a b k c
      refine ⟨⟨VNote.vadd a b k c, hnfo⟩, ?_⟩
      show vcode (VNote.vadd a b k c) = n
      rw [hmc, hae', hbe', hce']
      exact hdes

/-- On `ℕ`, the range of `gamma0Code` is exactly the set of codes the internal recogniser
accepts. -/
theorem isNF₁_iff_exists_gamma0Note (n : ℕ) :
    isNF₁ (V := ℕ) n ↔ ∃ o : Gamma0Note, gamma0Code o = n := by
  refine ⟨isNF₁_surj n, ?_⟩
  rintro ⟨o, rfl⟩
  have := isNF₁_gamma0ModelCode (V := ℕ) o
  simpa [gamma0ModelCode, gamma0Code] using this

end OrdinalAnalysis.Gentzen.VNoteBridge
