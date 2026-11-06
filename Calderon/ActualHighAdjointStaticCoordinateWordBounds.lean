import Calderon.ActualHighAdjointStaticEndpointJetBounds
import Calderon.LocalAffineCoordinateWordJetTransport

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic ActualReferenceLocalCoordinateWordJets
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets

attribute [local irreducible] referenceAdjointThreeHalfRadialFamily
  referenceHighAdjointCoordinateBoundaryFamily referenceRadialEndpointInvertibleLocus

theorem exists_referenceHighAdjoint_staticEndpoint_coordinate_word_bounds
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) :
    let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    let C0 : Fin 3 → (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun i z =>
      referenceHighAdjointCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z i
    let D : (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z =>
      deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧ d ≤ 1 ∧ ∀ N : ℕ,
      ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 ρ,
        ∀ beta : ℝ, 1 ≤ beta → ∀ i : Fin 3,
          HasCoordinateWordJetBound N (fun y => C0 i (q,(y,0))) x M beta 0 ∧
          HasCoordinateWordJetBound N (fun y => D (q,(y,0))) x M beta 0 := by
  intro Ω C0 D
  have hΩ : IsOpen Ω := isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hC0On (i : Fin 3) : ContDiffOn ℝ ∞ (C0 i) Ω := by
    intro z hz
    exact (contDiffAt_referenceHighAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg z i hz).contDiffWithinAt
  let A : (ℝ × (R3 × ℝ)) →
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hA : ContDiffOn ℝ ∞ A Ω :=
    contDiffOn_referenceAdjointThreeHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  have hDSmooth : ContDiffOn ℝ ∞ D Ω := contDiffOn_deriv_joint_radialSlice A Ω hΩ hA
  have hRaw := exists_referenceHighAdjoint_staticEndpoint_joint_jet_bounds
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  rcases hRaw with ⟨d,hd,hdρ,hd1,hAll⟩
  refine ⟨d,hd,hdρ,hd1,?_⟩
  intro N
  obtain ⟨M,hM,hBound⟩ := hAll N
  refine ⟨M,hM,?_⟩
  intro q hq x hx beta hbeta i
  have hz : (q,(x,(0 : ℝ))) ∈
      Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d) :=
    ⟨hq,hx,⟨neg_nonpos.mpr hd.le,hd.le⟩⟩
  have h := hBound (q,(x,0)) hz
  refine ⟨?_,?_⟩
  · intro w hw
    have hWord : ‖coordinateFieldWordPartial w (fun y => C0 i (q,(y,0))) x‖ ≤ M :=
      (norm_coordinateFieldWordPartial_joint_slice_le
        w (C0 i) Ω hΩ (hC0On i) q 0 x h.1).trans (((h.2.2 i).2 w.length hw).1)
    exact hWord.trans (by simpa only [Nat.zero_add,mul_one] using
      mul_le_mul_of_nonneg_left (one_le_pow₀ hbeta : 1 ≤ beta^w.length) hM)
  · intro w hw
    have hWord : ‖coordinateFieldWordPartial w (fun y => D (q,(y,0))) x‖ ≤ M :=
      (norm_coordinateFieldWordPartial_joint_slice_le
        w D Ω hΩ hDSmooth q 0 x h.1).trans (((h.2.2 i).2 w.length hw).2)
    exact hWord.trans (by simpa only [Nat.zero_add,mul_one] using
      mul_le_mul_of_nonneg_left (one_le_pow₀ hbeta : 1 ≤ beta^w.length) hM)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceHighAdjoint_staticEndpoint_coordinate_word_bounds
