import Calderon.ActualNormalizedSmoothSourceKernelBundle
import Calderon.MetricHessianDivergence
import Calderon.FixedExteriorSourceBall

/-!
These are proposition definitions only. No inhabitant or axiom is introduced here.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric TopologicalSpace
open scoped ENNReal ContDiff Distributions Topology

namespace OAI.AnisotropicCalderon.ExteriorSource.Literature
open EnergyBridge DirichletFamily MetricVolume

/-- A representative of the ACTUAL existing native solution for each fixed source.
The point and derivative values below belong to this same representative.
The source is not replaced by a free abstract inverse operator. -/
def IsRadiusTwoSmoothSourceResponse
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (response : 𝓓(fixedExteriorSourceOpens, ℝ) → R3 → ℝ) : Prop :=
  ∀ f : 𝓓(fixedExteriorSourceOpens, ℝ),
    ContDiffOn ℝ ∞ (response f) (radiusTwoOpens : Set R3) ∧
    ContinuousOn (response f) (closedBall (0 : R3) 2) ∧
    (response f =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
      (TauCeti.W1p.value
        (radiusTwoSourceSolution g hg
          (smoothRadiusTwoForcing ⟨(f : R3 → ℝ), f.contDiff⟩) : RadiusTwoH1) : R3 → ℝ)) ∧
    (∀ x : R3, ‖x‖ = 2 → response f x = 0)

/-- Existence of a smooth source response from the regularity interfaces; it rules
out a vacuous separation application. The proof uses the regularity interfaces,
interior representatives and the Euclidean-collar boundary barrier.
This proposition is not a literature assumption. -/
def RadiusTwoSmoothSourceResponseFromRegularity : Prop :=
  FixedDirichletRegularity → FixedSobolevCalculus →
    ∀ (g : MatrixField) (hg : IsAdmissibleMetric g),
      ∃ response : 𝓓(fixedExteriorSourceOpens, ℝ) → R3 → ℝ,
        IsRadiusTwoSmoothSourceResponse g hg response

/-- The exact A.7(a,b) consequence, with same native response witnesses.
Nonzero evaluation at an interior point is a separate consequence of part (a)
by selecting a boundary point, where the response predicate gives zero. -/
def RadiusTwoSourceSeparation : Prop :=
  ∀ (g : MatrixField) (hg : IsAdmissibleMetric g)
    (response : 𝓓(fixedExteriorSourceOpens, ℝ) → R3 → ℝ),
    IsRadiusTwoSmoothSourceResponse g hg response →
    (∀ p ∈ (radiusTwoOpens : Set R3),
      ∀ q ∈ closedBall (0 : R3) 2, p ≠ q →
        ∃ f : 𝓓(fixedExteriorSourceOpens, ℝ), response f p ≠ response f q) ∧
    (∀ p ∈ (radiusTwoOpens : Set R3), ∀ ξ : R3 →L[ℝ] ℝ,
      ∃ f : 𝓓(fixedExteriorSourceOpens, ℝ), fderiv ℝ (response f) p = ξ)

/-- Literal native dx operator, with the existing A_g = vol(g) g^{-1}. -/
def nativeMetricDifferential (g : MatrixField) (u : R3 → ℝ) (x : R3) : ℝ :=
  -(∑ i : Fin 3, fderiv ℝ
    (fun z : R3 => ∑ j : Fin 3, principalCoefficient g z i j *
      fderiv ℝ u z (coordinateVector j)) x (coordinateVector i))

/-- The exact coordinate PDE restriction on a symmetric raw 2-jet.
The value component is unrestricted because there is no zero order term. -/
def nativeMetricJetFunctional (g : MatrixField) (p : R3)
    (ξ : R3 →L[ℝ] ℝ) (H : R3 →L[ℝ] (R3 →L[ℝ] ℝ)) : ℝ :=
  -(∑ i : Fin 3, ∑ j : Fin 3,
    (fderiv ℝ (fun z : R3 => principalCoefficient g z i j) p (coordinateVector i) *
      ξ (coordinateVector j) +
    principalCoefficient g p i j * H (coordinateVector i) (coordinateVector j)))

/-- The coordinate consequence of A.5 on a local ball with its full
boundary as Gamma. No source-generated 2-jet endpoint is assumed here. -/
def LocalMetricHarmonicTwoJets : Prop :=
  ∀ (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3) (r : ℝ),
    0 < r → closedBall p r ⊆ (radiusTwoOpens : Set R3) →
    ∀ (a : ℝ) (ξ : R3 →L[ℝ] ℝ) (H : R3 →L[ℝ] (R3 →L[ℝ] ℝ)),
      (∀ v w : R3, H v w = H w v) → nativeMetricJetFunctional g p ξ H = 0 →
      ∃ u : R3 → ℝ, ContDiffOn ℝ ∞ u (ball p r) ∧
        (∀ x ∈ ball p r, nativeMetricDifferential g u x = 0) ∧
        u p = a ∧ fderiv ℝ u p = ξ ∧ fderiv ℝ (fderiv ℝ u) p = H

/-- A.6 specialized to smooth harmonic targets in native H^5.
The Sobolev-to-jet evaluation map and finite-dimensional closed-range
argument are not part of this statement.
The geometric connected-complement and disjoint-closure conditions are
retained literally and must be established at each application. -/
def RadiusTwoSmoothTargetSourceRunge : Prop :=
  ∀ (g : MatrixField) (hg : IsAdmissibleMetric g)
    (response : 𝓓(fixedExteriorSourceOpens, ℝ) → R3 → ℝ),
    IsRadiusTwoSmoothSourceResponse g hg response →
    ∀ (p : R3) (r : ℝ), 0 < r →
      closedBall p r ⊆ (radiusTwoOpens : Set R3) →
      Disjoint
        (closedBall fixedExteriorSourceCenter (1 / 8 : ℝ))
        (closedBall p r) →
      IsConnected (closedBall (0 : R3) 2 \ closedBall p r) →
      let U : Opens R3 := ⟨ball p r, isOpen_ball⟩
      ∀ (u : TauCeti.Wkp (volume : Measure R3) U 2 5) (uSmooth : R3 → ℝ),
        ContDiffOn ℝ ∞ uSmooth (U : Set R3) →
        ((TauCeti.Wkp.value 5 u : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict U] uSmooth) →
        (∀ x ∈ (U : Set R3), nativeMetricDifferential g uSmooth x = 0) →
        ∀ ε : ℝ, 0 < ε →
          ∃ (f : 𝓓(fixedExteriorSourceOpens, ℝ))
            (v : TauCeti.Wkp (volume : Measure R3) U 2 5),
            ((TauCeti.Wkp.value 5 v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict U]
              response f) ∧ ‖v - u‖ < ε

end OAI.AnisotropicCalderon.ExteriorSource.Literature

#print axioms OAI.AnisotropicCalderon.ExteriorSource.Literature.IsRadiusTwoSmoothSourceResponse
#print axioms OAI.AnisotropicCalderon.ExteriorSource.Literature.RadiusTwoSmoothSourceResponseFromRegularity
#print axioms OAI.AnisotropicCalderon.ExteriorSource.Literature.RadiusTwoSourceSeparation
#print axioms OAI.AnisotropicCalderon.ExteriorSource.Literature.nativeMetricDifferential
#print axioms OAI.AnisotropicCalderon.ExteriorSource.Literature.nativeMetricJetFunctional
#print axioms OAI.AnisotropicCalderon.ExteriorSource.Literature.LocalMetricHarmonicTwoJets
#print axioms OAI.AnisotropicCalderon.ExteriorSource.Literature.RadiusTwoSmoothTargetSourceRunge
