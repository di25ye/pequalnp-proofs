import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1601_aux

theorem no_four_of_girth_five {V : Type*} (H : SimpleGraph V)
    (hgirth : ∀ (p : V) (q : H.Walk p p), q.IsCycle → 5 ≤ q.length) :
    ∀ a b c d : V, a ≠ c → b ≠ d →
      ¬ (H.Adj a b ∧ H.Adj b c ∧ H.Adj c d ∧ H.Adj d a) := by
  intro a b c d hac hbd hadj
  rcases hadj with ⟨hab, hbc, hcd, hda⟩
  let W : H.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
  have hlen : W.length = 4 := rfl
  have hcycle : W.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨?_, by omega⟩
    simp only [W, SimpleGraph.Walk.tail_cons]
    simp [hab.ne.symm, hbc.ne, hcd.ne, hda.ne, hac.symm, hbd]
  have hge := hgirth a W hcycle
  omega

end PEqualNP.Outside.L_meta_1601_aux

theorem PEqualNP.Outside.L_meta_1601 : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ (p : Fin m) (q : H.Walk p p), q.IsCycle → 5 ≤ q.length) → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ y : Fin m → Bool, PEqualNP.EdgeOwnership.gateVal m D k y = true → PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ y = true) → ∃ S : Finset (Fin m), (∀ e w : Fin m, H.Adj e w → e ∈ S ∨ w ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 ∧ H.edgeFinset.card ≤ D.size + 1 := by
  intro hbound m H inst D hmono heval hgirth hclean
  have hno4 : ∀ a b c d : Fin m, a ≠ c → b ≠ d →
      ¬ (H.Adj a b ∧ H.Adj b c ∧ H.Adj c d ∧ H.Adj d a) := by
    exact PEqualNP.Outside.L_meta_1601_aux.no_four_of_girth_five H hgirth
  have hmono' : ∀ g ∈ D.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    simpa using hmono g hg
  have heval' : ∀ x : Fin m → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨D.gates, D.output⟩ (List.ofFn x) =
        decide (∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true) := by
    intro x
    simpa [PEqualNP.MetaComplexity.circuitFun,
      PEqualNP.MetaComplexity.NestedCover.graphFun] using congrFun heval x
  have hclean' : ∀ (i : Fin D.gates.length) (x : Fin m → Bool),
      (D.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨D.gates, 0⟩
        (List.ofFn x)).getD (m + (i : ℕ)) false = true →
      ∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true := by
    intro i x hi hv
    have hop : (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op =
        PEqualNP.CircuitLowerBounds.GateOp.and := by
      simpa [PEqualNP.MetaComplexity.NestedCover.gateAt,
        List.getD_eq_getElem, List.get_eq_getElem] using hi
    have hval : PEqualNP.EdgeOwnership.gateVal m D i x = true := hv
    have hx := hclean i i.isLt hop x hval
    simpa [PEqualNP.MetaComplexity.NestedCover.graphFun] using hx
  obtain ⟨S, hcover, hcount⟩ := hbound m H hno4 D.gates D.output hmono' heval' hclean'
  refine ⟨S, hcover, ?_, ?_⟩
  · simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hcount
  · change H.edgeFinset.card ≤ D.gates.length + 1
    omega
