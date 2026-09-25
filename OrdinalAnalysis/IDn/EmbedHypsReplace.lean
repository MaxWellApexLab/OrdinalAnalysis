/- Bridges `OrdinalAnalysis.IDn.Evaluate`'s term-replacement section (`Sim`, `sim_subst_numI`,
`IDnDerivable.replace_head`, all green/merged) into `OrdinalAnalysis.IDn.Embed`'s
`EmbedHyps.replaceHeadNumI` field, once that field carries the hypothesis `φ'.freeVariables = ∅`
it needs (added to `Embed.lean` alongside this file — see `taut`'s sibling field, one line above
`replaceHeadNumI`, for the same closedness-hypothesis pattern already used there).

Freund's remark in the proof of Proposition 6.4: a closed term `t` in the head formula's
substitution slot may be replaced by the numeral of its value, for *some* value `v`. Concretely,
`v := closedVal t`, and `Sim (φ'/[t]) (φ'/[numI (closedVal t)])` is exactly `sim_subst_numI`, so
`IDnDerivable.replace_head` transports a derivation of the head across it. This is the whole
proof; no new metatheorem, no induction on `d`. -/
import OrdinalAnalysis.IDn.Evaluate

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting
open LO.FirstOrder.Arithmetic

variable {n : ℕ} {A : Fin n → Semisentence (LXIn n) 1}

/-- **`EmbedHyps.replaceHeadNumI`, proved**: term replacement at the head, specialised to a
numeral witness, composed from `Evaluate.lean`'s `sim_subst_numI` (a closed term and the
numeral of its value are `Sim`-related, given the head formula is closed and `X`-free) and
`IDnDerivable.replace_head` (term replacement transports a derivation of the head). -/
theorem embedHyps_replaceHeadNumI {ρ : ThetaWNoteD} {H : Set ThetaWNoteD → Set ThetaWNoteD}
    {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)} {φ' : Semiformula (LIinfN n) ℕ 1}
    (t : SyntacticTerm (LIinfN n)) (hφ' : φ'.freeVariables = ∅) (ht : t.freeVariables = ∅)
    (hX : XFreeI φ') (hA : ∀ j, XFreeL (A j)) (hH : ThetaWNoteD.IsOperator H)
    (d : IDnDerivable A ρ H α (φ'/[t] :: Γ)) :
    ∃ v : ℕ, IDnDerivable A ρ H α (φ'/[numI v] :: Γ) :=
  ⟨closedVal t, d.replace_head hA hH (sim_subst_numI hφ' hX ht)⟩

end IDn

end OrdinalAnalysis
