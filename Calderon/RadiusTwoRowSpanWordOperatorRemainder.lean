import Calderon.RadiusTwoCanonicalRowSpanWordEvaluations
import Calderon.NativeCoordinateOperatorBounds
import Calderon.NativeCoordinateExpansion
import Mathlib.Topology.DenseEmbedding

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily ActualReferenceDDHigherGeometryJets ReferenceDensityBounds
  ActualReferenceLocalCoordinateWordJets

lemma norm_radiusTwo_rowSpan_word_operator_remainder_le
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (S P Z : Set R3) (hPB : P ⊆ (radiusTwoOpens : Set R3) \ S)
    (hZ : IsOpen Z) (hConvex : Convex ℝ Z)
    (hZB : Z ⊆ (radiusTwoOpens : Set R3)) (hZS : Z ⊆ S) :
    let ν : Measure R3 := ((volume : Measure R3).restrict radiusTwoOpens).restrict S
    let R : RadiusTwoL2 →L[ℝ] Lp ℝ 2 ν := MeasureTheory.LpToLpRestrictCLM R3 ℝ ℝ
      ((volume : Measure R3).restrict radiusTwoOpens) 2 S
    let F : P → Lp ℝ 2 ν := fun p => R (K ⟨p,(hPB p.property).1⟩)
    let Y : Submodule ℝ (Lp ℝ 2 ν) :=
      (Submodule.span ℝ (Set.range F)).topologicalClosure
    let liftRows : P → Y := fun p => ⟨F p,
      (Submodule.le_topologicalClosure _)
        (Submodule.subset_span (show F p ∈ Set.range F from ⟨p,rfl⟩))⟩
    let e : (P →₀ ℝ) →ₗ[ℝ] Y := Finsupp.linearCombination ℝ liftRows
    ∀ (C : ℕ → ℝ), (∀ n : ℕ, 0 ≤ C n) →
      ∀ (L : List (Fin 3) → R3 → Y →L[ℝ] ℝ),
        DenseRange e →
        (∀ w : List (Fin 3), ∀ z ∈ Z, ‖L w z‖ ≤ C w.length) →
        (∀ w : List (Fin 3), ∀ z ∈ Z, ∀ c : P →₀ ℝ,
          L w z (e c) = Finsupp.linearCombination ℝ
            (fun p : P => coordinateFieldWordPartial w (G ⟨p,(hPB p.property).1⟩) z) c) →
        ∀ (w : List (Fin 3)) (x y : R3), x ∈ Z → y ∈ Z →
          let A : R3 →L[ℝ] (Y →L[ℝ] ℝ) :=
            coordinateExpansion (fun i : Fin 3 => L (i::w) x)
          ‖L w y - L w x - A (y-x)‖ ≤ 9 * C (w.length+2) * ‖y-x‖^2 := by
  classical
  intro ν R F Y liftRows e C hC L hDense hNorm hAction w x y hx hy A
  have hSmooth := IsRadiusTwoSymmetricInverseSourceKernel.separatelySmooth
    hreg hcalc g hg K G hData
  have hRows (p : P) : ContDiffOn ℝ ∞ (G ⟨p,(hPB p.property).1⟩) Z := by
    apply (hSmooth.2.1 ⟨p,(hPB p.property).1⟩).mono
    intro z hz
    refine ⟨hZB hz,?_⟩
    intro hEqual
    have hpS : (p : R3) ∈ S := (mem_singleton_iff.mp hEqual) ▸ hZS hz
    exact (hPB p.property).2 hpS
  let T : Y →L[ℝ] ℝ := L w y - L w x - A (y-x)
  let D : ℝ := 9 * C (w.length+2) * ‖y-x‖^2
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (by norm_num) (hC _)) (sq_nonneg _)
  have hSigned (c : P →₀ ℝ) : ‖T (e c)‖ ≤ D * ‖e c‖ := by
    let U : R3 → ℝ := fun z => ∑ p : ↥c.support,
      c p • G ⟨(p : P),(hPB (p : P).property).1⟩ z
    have hWeighted (p : ↥c.support) : ContDiffOn ℝ ∞
        (fun z => c p • G ⟨(p : P),(hPB (p : P).property).1⟩ z) Z :=
      (hRows (p : P)).const_smul (c p)
    have hU : ContDiffOn ℝ ∞ U Z := by
      apply ContDiffOn.sum
      intro p _
      exact hWeighted p
    have hWord (u : List (Fin 3)) (z : R3) (hz : z ∈ Z) :
        coordinateFieldWordPartial u U z = L u z (e c) := by
      have hSum : (∑ p : ↥c.support, c p • coordinateFieldWordPartial u
          (G ⟨(p : P),(hPB (p : P).property).1⟩) z) =
          Finsupp.linearCombination ℝ
            (fun p : P => coordinateFieldWordPartial u (G ⟨p,(hPB p.property).1⟩) z) c := by
        change (∑ p : ↥c.support, c p • coordinateFieldWordPartial u
          (G ⟨(p : P),(hPB (p : P).property).1⟩) z) =
          ∑ p ∈ c.support, c p • coordinateFieldWordPartial u
            (G ⟨p,(hPB p.property).1⟩) z
        exact Finset.sum_coe_sort
          (f := fun p : P => c p • coordinateFieldWordPartial u
            (G ⟨p,(hPB p.property).1⟩) z) (s := c.support)
      calc
        coordinateFieldWordPartial u U z = ∑ p : ↥c.support,
            coordinateFieldWordPartial u
              (fun a => c p • G ⟨(p : P),(hPB (p : P).property).1⟩ a) z :=
          coordinateFieldWordPartial_sum_of_isOpen u _ Z hZ hWeighted z hz
        _ = ∑ p : ↥c.support, c p • coordinateFieldWordPartial u
            (G ⟨(p : P),(hPB (p : P).property).1⟩) z := by
          apply Finset.sum_congr rfl
          intro p _
          exact congrFun (coordinateFieldWordPartial_const_smul u (c p)
            (G ⟨(p : P),(hPB (p : P).property).1⟩)) z
        _ = _ := hSum.trans (hAction u z hz c).symm
    let f : R3 → ℝ := coordinateFieldWordPartial w U
    have hf : ContDiffOn ℝ ∞ f Z :=
      contDiffOn_coordinateFieldWordPartial w U Z hZ hU
    have hFirst (i : Fin 3) : coordinateFieldWordPartial [i] f =
        coordinateFieldWordPartial (i::w) U := by
      simp only [coordinateFieldWordPartial, f]
    have hSecond (i j : Fin 3) : coordinateFieldWordPartial [j,i] f =
        coordinateFieldWordPartial (j::i::w) U := by
      simp only [coordinateFieldWordPartial, f]
    have hSecondBound (z : R3) (hz : z ∈ Z) (i j : Fin 3) :
        ‖coordinateFieldWordPartial [j,i] f z‖ ≤ C (w.length+2) * ‖e c‖ := by
      rw [hSecond i j, hWord (j::i::w) z hz]
      exact ((L (j::i::w) z).le_opNorm (e c)).trans
        (mul_le_mul_of_nonneg_right
          (by simpa only [List.length_cons] using hNorm (j::i::w) z hz) (norm_nonneg _))
    have hM : 0 ≤ C (w.length+2) * ‖e c‖ := mul_nonneg (hC _) (norm_nonneg _)
    have hRem := norm_firstOrder_remainder_le_of_fderiv_lipschitz f Z hConvex
      (9 * (C (w.length+2) * ‖e c‖)) (mul_nonneg (by norm_num) hM)
      (fun z hz => (hf.contDiffAt (hZ.mem_nhds hz)).differentiableAt (by simp))
      (fun z hz z' hz' => by
        have h := norm_fderiv_sub_le_nine_mul_of_coordinateWord_two_bound
          f Z hZ hConvex hf (C (w.length+2) * ‖e c‖) hM hSecondBound z' z hz' hz
        simpa only [norm_sub_rev] using h)
      x y hx hy
    have hLinear : fderiv ℝ f x (y-x) = (A (y-x)) (e c) := by
      calc
        fderiv ℝ f x (y-x) = ∑ i : Fin 3,
            (y-x) i • coordinateFieldWordPartial [i] f x :=
          ActualReferenceDecomposition.fderiv_apply_eq_coordinate_sum f x (y-x)
        _ = ∑ i : Fin 3, (y-x) i • L (i::w) x (e c) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hFirst i, hWord (i::w) x hx]
        _ = (A (y-x)) (e c) := by
          simp only [A, coordinateExpansion_apply, sum_apply, smul_apply]
    have hValue : T (e c) = f y - f x - fderiv ℝ f x (y-x) := by
      change L w y (e c) - L w x (e c) - (A (y-x)) (e c) = _
      rw [← hWord w y hy, ← hWord w x hx, ← hLinear]
    calc
      ‖T (e c)‖ = ‖f y - f x - fderiv ℝ f x (y-x)‖ := congrArg norm hValue
      _ ≤ (9 * (C (w.length+2) * ‖e c‖)) * ‖y-x‖^2 := hRem
      _ = D * ‖e c‖ := by dsimp only [D]; ring
  have hAll : ∀ v : Y, ‖T v‖ ≤ D * ‖v‖ :=
    isClosed_property hDense
      (isClosed_le T.continuous.norm (continuous_const.mul continuous_norm)) hSigned
  exact T.opNorm_le_bound hD hAll

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.norm_radiusTwo_rowSpan_word_operator_remainder_le
