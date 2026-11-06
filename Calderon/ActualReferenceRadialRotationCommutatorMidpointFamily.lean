import Calderon.ActualReferenceRadialRotationCommutatorJointJets
import Calderon.ActualReferenceSharpMidpointRadialTrace

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

/-! Full upfront argument: EXPANSION-v001.json. Reuse the EXISTING bounded linear
compatible interpolation family and its existing smooth kernel restriction. This
auxiliary family has that construction's explicit zero extension outside the original
inverse locus; actual derivative identities and smoothness are asserted on the locus. -/

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceRadialRotationCommutatorEndpointPairFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ)) : SphereSobolevEndpointPair :=
  (referenceLowerRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p,
   referenceSharpRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p)

lemma referenceRadialRotationCommutatorEndpointPairFamily_mem_compatible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceRadialRotationCommutatorEndpointPairFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p ∈ sphereSobolevCompatibleEndpoints := by
  change (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp
      (referenceSharpRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p) =
    (referenceLowerRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  have hInc := sphereSobolevInclusionL_negative_half_notation_eq (1/2:ℝ)
    (by norm_num) (by norm_num)
  have hComp := congrArg
    (fun A : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      A.comp (referenceSharpRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p)) hInc
  exact hComp.trans (referenceLowerRadialRotationCommutatorL_upper_compatibility
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hp.2.2 hp.1 hp.2.1)

def referenceRadialRotationCommutatorMidpointFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) : (ℝ × (R3 × ℝ)) → (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
  sphereSobolevCompatibleInterpolationFamily
    (referenceRadialRotationCommutatorEndpointPairFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j)
    (referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (referenceRadialRotationCommutatorEndpointPairFamily_mem_compatible
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j)

lemma referenceRadialRotationCommutatorMidpointFamily_of_mem
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceRadialRotationCommutatorMidpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p =
    sphereSobolevMidpointL
      (referenceLowerRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p)
      (referenceSharpRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p)
      (referenceRadialRotationCommutatorEndpointPairFamily_mem_compatible
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hp) :=
  sphereSobolevCompatibleInterpolationFamily_of_mem
    (referenceRadialRotationCommutatorEndpointPairFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j)
    (referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (referenceRadialRotationCommutatorEndpointPairFamily_mem_compatible
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) p hp

lemma norm_referenceRadialRotationCommutatorMidpointFamily_le
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ‖referenceRadialRotationCommutatorMidpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p‖ ≤
    (‖referenceLowerRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p‖ +
     ‖referenceSharpRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p‖)/2 := by
  rw [referenceRadialRotationCommutatorMidpointFamily_of_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hp]
  exact norm_sphereSobolevMidpointL_le _ _ _

lemma referenceRadialRotationCommutatorMidpointFamily_upper_inclusion
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (referenceRadialRotationCommutatorMidpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p).comp
      (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      (referenceSharpRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p) := by
  rw [referenceRadialRotationCommutatorMidpointFamily_of_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hp]
  exact sphereSobolevMidpointL_inclusion _ _ _

lemma contDiffOn_referenceRadialRotationCommutatorMidpointFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) :
    ContDiffOn ℝ ∞ (referenceRadialRotationCommutatorMidpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j)
      (referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  have hPair : ContDiffOn ℝ ∞ (referenceRadialRotationCommutatorEndpointPairFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j)
      (referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
    intro p hp
    exact ((contDiffAt_referenceLowerRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hp.2.2 hp.2.1).prodMk
        (contDiffAt_referenceSharpRadialRotationCommutatorL
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hp.1 hp.2.1)).contDiffWithinAt
  exact contDiffOn_sphereSobolevCompatibleInterpolationFamily
    (referenceRadialRotationCommutatorEndpointPairFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j)
    (referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (isOpen_referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (referenceRadialRotationCommutatorEndpointPairFamily_mem_compatible
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) hPair

lemma contDiffAt_referenceRadialRotationCommutatorMidpointFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (referenceRadialRotationCommutatorMidpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) p :=
  (contDiffOn_referenceRadialRotationCommutatorMidpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j).contDiffAt
      ((isOpen_referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds hp)

theorem exists_reference_commonRadius_radialRotationCommutatorMidpoint_jets
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∀ N : ℕ,
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ p ∈ Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ),
          p ∈ referenceRadialEndpointInvertibleLocus
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
          ∀ i j : Fin 3,
            ContDiffAt ℝ ∞ (referenceRadialRotationCommutatorMidpointFamily
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) p ∧
            ∀ k : ℕ, k ≤ N →
              ‖iteratedFDeriv ℝ k (referenceRadialRotationCommutatorMidpointFamily
                g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) p‖ ≤ M := by
  classical
  obtain ⟨δ,hδ,hδρ,hRoom⟩ := exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  let K : Set (ℝ × (R3 × ℝ)) :=
    Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ)
  let Cij : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) → (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
    referenceRadialRotationCommutatorMidpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hK : IsCompact K :=
    isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)
  have hSmooth : ∀ i j : Fin 3, ∀ p ∈ K, ContDiffAt ℝ ∞ (Cij i j) p := by
    intro i j p hp
    exact contDiffAt_referenceRadialRotationCommutatorMidpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p (hRoom hp)
  refine ⟨δ,hδ,hδρ,?_⟩
  intro N
  have hb (i j : Fin 3) : ∃ M : ℝ, 0 ≤ M ∧
      ∀ k : ℕ, k ≤ N → ∀ p ∈ K, ‖iteratedFDeriv ℝ k (Cij i j) p‖ ≤ M :=
    exists_compact_iteratedFDeriv_bound (Cij i j) K hK (hSmooth i j) N
  let Mij : Fin 3 → Fin 3 → ℝ := fun i j => Classical.choose (hb i j)
  have hM (i j : Fin 3) : 0 ≤ Mij i j ∧
      ∀ k : ℕ, k ≤ N → ∀ p ∈ K, ‖iteratedFDeriv ℝ k (Cij i j) p‖ ≤ Mij i j :=
    Classical.choose_spec (hb i j)
  have hSum (i : Fin 3) : 0 ≤ ∑ j : Fin 3, Mij i j :=
    Finset.sum_nonneg (fun j _ => (hM i j).1)
  refine ⟨∑ i : Fin 3, ∑ j : Fin 3, Mij i j,
    Finset.sum_nonneg (fun i _ => hSum i),?_⟩
  intro p hp
  refine ⟨hRoom hp,?_⟩
  intro i j
  refine ⟨hSmooth i j p hp,?_⟩
  intro k hk
  exact ((hM i j).2 k hk p hp).trans
    ((Finset.single_le_sum (fun j' _ => (hM i j').1) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun i' _ => hSum i') (Finset.mem_univ i)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialRotationCommutatorEndpointPairFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialRotationCommutatorEndpointPairFamily_mem_compatible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialRotationCommutatorMidpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialRotationCommutatorMidpointFamily_of_mem
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_referenceRadialRotationCommutatorMidpointFamily_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialRotationCommutatorMidpointFamily_upper_inclusion
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceRadialRotationCommutatorMidpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceRadialRotationCommutatorMidpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_radialRotationCommutatorMidpoint_jets
