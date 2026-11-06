import Calderon.ActualFiniteHalfFormalAdjointPhysicalSection
import Calderon.ActualFormalAdjointPhysicalDensityOperator
import Calderon.ActualFiniteHighFullAdjointSecondSectionGraph
import Calderon.ActualDensityPrincipalFrameSmoothness

/-! Full AUTHOR upfront: actual-Y-second-action-domain-author-oct16-v001/
EXPANSION-finite-full-formal-adjoint-L2-v015.md object2 and refinement017.
Exact literal full formal-adjoint graph, no output regularity premise. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceFiniteHalfFormalAdjointPhysicalSection
  referenceFormalAdjointPhysicalDensityOperator referenceHighFullAdjointFirstAction
  referenceLowerFullAdjointFirstAction referenceFiniteHighFullAdjointFirstSection
  sphereSobolevInclusionL sphereSobolevPartialSumL referenceDensityPrincipalFrameCoefficient
  normalizedSecondDriftFrameJoint referenceMetricGramFrame referenceFrameConnectionCoefficient

lemma exists_reference_commonRadius_finiteFormalAdjointPhysicalSection_graph
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (hreg : FixedDirichletRegularity) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ ρ ∧
      ∀ (n : ℕ) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
      ∀ (R : R3 → ℝ), ContDiff ℝ ∞ R →
      ∀ (u : R3 → SphereSobolev (3/2 : ℝ)), ContDiff ℝ ∞ u → HasCompactSupport u →
      (∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < d0 ∧ R y ≠ 0) → ∀ y : R3,
        sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
          (referenceFiniteHalfFormalAdjointPhysicalSection
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 n q R u y) =
        referenceFormalAdjointPhysicalDensityOperator
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
          (fun x => sphereSobolevPartialSumL (3/2 : ℝ) n (u x)) y := by
  obtain ⟨d0,hd0,hdρ,hGraph⟩ := exists_reference_commonRadius_fullAdjointSecondSection_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  refine ⟨d0,hd0,hdρ,?_⟩
  intro n q hq R hR u hu hCompact hSupportRoom y
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Pn := sphereSobolevPartialSumL (3/2 : ℝ) n
  have hInput (c : R3 → ℝ) :
      (fun x => Pn (c x • u x)) = (fun x => c x • Pn (u x)) := by
    funext x
    exact Pn.map_smul (c x) (u x)
  have hOrdered (i j : Fin 3) :
      J (referenceHighFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun z => referenceFiniteHighFullAdjointFirstSection
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R
          (fun x => (R x * referenceDensityPrincipalFrameCoefficient g g2 L q x i j) • u x) z i) y j) =
      referenceLowerFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun z => referenceHighFullAdjointFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
          (fun x => (R x * referenceDensityPrincipalFrameCoefficient g g2 L q x i j) • Pn (u x)) z i) y j := by
    let c : R3 → ℝ := fun x => R x * referenceDensityPrincipalFrameCoefficient g g2 L q x i j
    let U : R3 → SphereSobolev (3/2 : ℝ) := fun x => c x • u x
    have hQ : ContDiff ℝ ∞ (fun x => referenceDensityPrincipalFrameCoefficient g g2 L q x i j) :=
      (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).comp
        (contDiff_const.prodMk contDiff_id)
    have hU : ContDiff ℝ ∞ U := (hR.mul hQ).smul hu
    have hUSupport : tsupport U ⊆ tsupport u := by
      apply closure_minimal ?_ (isClosed_tsupport u)
      intro x hx
      by_contra hxu
      have hZero : u x = 0 := image_eq_zero_of_notMem_tsupport hxu
      change U x ≠ 0 at hx
      exact hx (by simp only [U,hZero,smul_zero])
    have hSupportU : ∀ x ∈ tsupport U, ‖x-y0‖ < ρ ∧ |R x| < d0 ∧ R x ≠ 0 :=
      fun x hx => hSupportRoom x (hUSupport hx)
    have hG := hGraph n q hq R hR U hU hSupportU i j y
    have hTransport := congrArg
      (fun V : R3 → SphereSobolev (3/2 : ℝ) => referenceLowerFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun z => referenceHighFullAdjointFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R V z i) y j) (hInput c)
    exact hG.trans hTransport
  change J (referenceFiniteHalfFormalAdjointPhysicalSection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 n q R u y) = _
  simp only [referenceFiniteHalfFormalAdjointPhysicalSection,
    referenceFormalAdjointPhysicalDensityOperator,map_add,map_sub,map_sum]
  apply congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+z)
  · apply congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x-z)
    · apply Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      intro i hi
      apply Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      intro j hj
      exact hOrdered i j
    · apply Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      intro k hk
      exact congrArg
        (fun V : R3 → SphereSobolev (3/2 : ℝ) => J (referenceHighFullAdjointFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R V y k))
        (hInput (fun x => R x * ∑ i : Fin 3, ∑ j : Fin 3,
          referenceDensityPrincipalFrameCoefficient g g2 L q x i j *
            referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j))
  · apply Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    intro i hi
    exact congrArg
      (fun V : R3 → SphereSobolev (3/2 : ℝ) => J (referenceHighFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R V y i))
      (hInput (fun x => R x * normalizedSecondDriftFrameJoint g g2 L i (q,x)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_finiteFormalAdjointPhysicalSection_graph
