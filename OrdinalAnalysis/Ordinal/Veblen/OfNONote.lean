/-
  `NONote ↪ Gamma0Note`: Cantor normal forms are Veblen normal forms.

  `φ_0(b) = ω ^ b`, so `ONote.oadd e n a` — which denotes `ω ^ e · n + a` — translates to
  `VNote.vadd 0 e n a`, and the translation is an order embedding onto the notations below
  `ε₀ = φ_1(0)`.

  This is what lets the `ε₀`-level results already in the tree be read as statements about
  the new height type: a derivation carrying an `NONote` height carries a `Gamma0Note`
  height below `ε₀`, and `ofNONote_lt_epsilonNote_zero` says the image really does stop
  there.

  The two `ONote` facts used here (`repr o < ω ^ repr o` and `repr o < ε₀` for normal `o`)
  are proved locally: the first exists in `Ordinal/OmegaPow.lean` but is `private`, and the
  second is in neither mathlib nor this tree.
-/
import OrdinalAnalysis.Ordinal.Veblen.Instance

set_option autoImplicit false

namespace OrdinalAnalysis

open Ordinal

/-! ### Two facts about `ONote`

Both say that Cantor normal forms stay below `ε₀`, in the two forms the normal-form proof
below needs. -/

/-- Every Cantor normal form is strictly below its own `ω`-power.  This is what makes
`vadd 0 (ofONote e) n _` a *Veblen* normal form: the second argument of `φ_0` must not be a
fixed point of `φ_0 = ω ^ ·`, and no notation below `ε₀` is. -/
theorem ONote_repr_lt_omega0_opow :
    ∀ o : ONote, ONote.NF o → ONote.repr o < ω ^ ONote.repr o
  | 0, _ => by simp
  | ONote.oadd e n t, h => by
    have he : ONote.repr e < ONote.repr (ONote.oadd e n t) :=
      lt_of_lt_of_le (ONote_repr_lt_omega0_opow e h.fst) (ONote.omega0_le_oadd e n t)
    have ho : ONote.oadd e n t < ONote.oadd (ONote.oadd e n t) 1 0 :=
      ONote.oadd_lt_oadd_1 h he
    simpa [ONote.lt_def] using ho

/-- Every Cantor normal form denotes an ordinal below `ε₀ = φ_1(0)`. -/
theorem ONote_repr_lt_epsilon_zero :
    ∀ o : ONote, ONote.NF o → ONote.repr o < veblen 1 0
  | 0, _ => by simpa using veblen_pos
  | ONote.oadd e n a, h => by
    have hprin : IsPrincipal (· + ·) (veblen 1 0) := isPrincipal_add_veblen 1 0
    have hfix : ω ^ (veblen 1 0 : Ordinal) = veblen 1 0 := by
      have h0 := veblen_veblen_of_lt (o₁ := 0) (o₂ := 1) zero_lt_one 0
      rwa [veblen_zero_apply] at h0
    have hop : ω ^ ONote.repr e < veblen 1 0 := by
      rw [← hfix]
      exact (opow_lt_opow_iff_right one_lt_omega0).2 (ONote_repr_lt_epsilon_zero e h.fst)
    show ω ^ ONote.repr e * ((n : ℕ) : Ordinal) + ONote.repr a < veblen 1 0
    exact hprin (hprin.mul_natCast_lt hop _) (ONote_repr_lt_epsilon_zero a h.snd)

namespace VNote

/-! ### The translation -/

/-- Cantor normal forms as Veblen normal forms: `ω ^ e = φ_0(e)`. -/
def ofONote : ONote → VNote
  | 0 => 0
  | ONote.oadd e n a => VNote.vadd 0 (ofONote e) n (ofONote a)

@[simp] theorem ofONote_zero : ofONote 0 = 0 := rfl

@[simp] theorem ofONote_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    ofONote (ONote.oadd e n a) = VNote.vadd 0 (ofONote e) n (ofONote a) := rfl

@[simp] theorem repr_ofONote : ∀ o : ONote, repr (ofONote o) = ONote.repr o
  | 0 => rfl
  | ONote.oadd e n a => by
    show veblen (repr (0 : VNote)) (repr (ofONote e)) * ((n : ℕ) : Ordinal)
        + repr (ofONote a)
        = ω ^ ONote.repr e * ((n : ℕ) : Ordinal) + ONote.repr a
    rw [repr_zero, veblen_zero_apply, repr_ofONote e, repr_ofONote a]

theorem nf_ofONote : ∀ {o : ONote}, ONote.NF o → NF (ofONote o)
  | 0, _ => NF.zero
  | ONote.oadd e n a, h => by
    rw [ofONote_oadd]
    refine NF.vadd NF.zero (nf_ofONote h.fst) (nf_ofONote h.snd) ?_ ?_
    · rw [repr_zero, veblen_zero_apply]
      simp only [repr_ofONote]
      exact ONote_repr_lt_omega0_opow e h.fst
    · rw [repr_zero, veblen_zero_apply]
      simp only [repr_ofONote]
      exact h.snd'.repr_lt

end VNote

namespace Gamma0Note

/-- The embedding of the `ε₀` notations into the `Γ₀` notations. -/
def ofNONote (x : NONote) : Gamma0Note :=
  ⟨VNote.ofONote x.1, VNote.nf_ofONote x.2⟩

@[simp] theorem repr_ofNONote (x : NONote) : repr (ofNONote x) = ONote.repr x.1 :=
  VNote.repr_ofONote x.1

theorem ofNONote_lt_ofNONote {x y : NONote} (h : x < y) : ofNONote x < ofNONote y := by
  rw [lt_def, repr_ofNONote, repr_ofNONote]
  exact h

theorem ofNONote_strictMono : StrictMono ofNONote := fun _ _ h => ofNONote_lt_ofNONote h

theorem ofNONote_injective : Function.Injective ofNONote :=
  ofNONote_strictMono.injective

/-- The image of the embedding is exactly the notations below `ε₀`. -/
theorem ofNONote_lt_epsilonNote_zero (x : NONote) : ofNONote x < epsilonNote 0 := by
  rw [lt_def, repr_ofNONote, repr_epsilonNote, repr_zero]
  exact ONote_repr_lt_epsilon_zero x.1 x.2

/-- `ofNONote` as an order embedding. -/
def ofNONoteEmbedding : NONote ↪o Gamma0Note where
  toFun := ofNONote
  inj' := ofNONote_injective
  map_rel_iff' := by
    intro x y
    show ofNONote x ≤ ofNONote y ↔ x ≤ y
    constructor
    · intro h
      by_contra hc
      exact absurd (ofNONote_lt_ofNONote (lt_of_not_ge hc)) (not_lt_of_ge h)
    · intro h
      rcases lt_or_eq_of_le h with h | rfl
      · exact le_of_lt (ofNONote_lt_ofNONote h)
      · exact le_rfl

@[simp] theorem coe_ofNONoteEmbedding : ⇑ofNONoteEmbedding = ofNONote := rfl

end Gamma0Note

end OrdinalAnalysis
