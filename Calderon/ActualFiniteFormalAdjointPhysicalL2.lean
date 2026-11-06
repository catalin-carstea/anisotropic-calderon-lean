import Calderon.ActualFiniteHalfFormalAdjointPhysicalGraph
import Calderon.ActualFiniteHalfFormalAdjointPhysicalGlobal
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Full AUTHOR upfront: actual-Y-second-action-domain-author-oct16-v001/
EXPANSION-finite-full-formal-adjoint-L2-v015.md, object4.
One global SphereL2 representative of literal formal Pdag on ORIGINAL finite input. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceFiniteHalfFormalAdjointPhysicalSection
  referenceFormalAdjointPhysicalDensityOperator sphereSobolevPartialSumL
  sphereSobolevInclusionL sphereSobolevZeroEquiv

lemma exists_reference_commonRadius_finiteFormalAdjointPhysical_L2
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (hreg : FixedDirichletRegularity) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      ∀ (n : ℕ) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
      ∀ (R : R3 → ℝ), ContDiff ℝ ∞ R →
      ∀ (u : R3 → SphereSobolev (3/2 : ℝ)), ContDiff ℝ ∞ u → HasCompactSupport u →
      (∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < δ ∧ R y ≠ 0) →
      ∃ f : R3 → SphereL2, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
        MemLp f 2 (volume : Measure R3) ∧ ∀ y : R3,
          sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
            (sphereSobolevZeroEquiv hO hD (f y)) =
          referenceFormalAdjointPhysicalDensityOperator
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
            (fun z => sphereSobolevPartialSumL (3/2 : ℝ) n (u z)) y := by
  obtain ⟨dG,hdG,hdGρ,hGraph⟩ := exists_reference_commonRadius_finiteFormalAdjointPhysicalSection_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 hreg
  obtain ⟨dS,hdS,hdSρ,hGlobal⟩ := exists_reference_commonRadius_finiteFormalAdjointPhysicalSection_global
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 hreg
  refine ⟨min dG dS,lt_min hdG hdS,(min_le_left _ _).trans hdGρ,?_⟩
  intro n q hq R hR u hu hCompact hSupportRoom
  have hSupportG : ∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < dG ∧ R y ≠ 0 := by
    intro y hy
    have hs := hSupportRoom y hy
    exact ⟨hs.1,hs.2.1.trans_le (min_le_left _ _),hs.2.2⟩
  have hSupportS : ∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < dS ∧ R y ≠ 0 := by
    intro y hy
    have hs := hSupportRoom y hy
    exact ⟨hs.1,hs.2.1.trans_le (min_le_right _ _),hs.2.2⟩
  let W : R3 → SphereSobolev (1/2 : ℝ) := fun y => referenceFiniteHalfFormalAdjointPhysicalSection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 n q R u y
  have hWG := hGraph n q hq R hR u hu hCompact hSupportG
  have hWS : ContDiff ℝ ∞ W ∧ HasCompactSupport W :=
    hGlobal n q hq R hR u hu hCompact hSupportS
  let Z := sphereSobolevZeroEquiv hO hD
  let I0 := sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let T0 : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereL2 :=
    Z.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp I0
  let f : R3 → SphereL2 := fun y => Z.symm (I0 (W y))
  have hfSmooth : ContDiff ℝ ∞ f := T0.contDiff.comp hWS.1
  have hfSupport : tsupport f ⊆ tsupport W := tsupport_comp_subset (map_zero T0) W
  have hfCompact : HasCompactSupport f :=
    hWS.2.of_isClosed_subset (isClosed_tsupport f) hfSupport
  have hfMem : MemLp f 2 (volume : Measure R3) :=
    hfSmooth.continuous.memLp_of_hasCompactSupport hfCompact
  refine ⟨f,hfSmooth,hfCompact,hfMem,?_⟩
  intro y
  have hCancel := congrArg (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num))
    (Z.apply_symm_apply (I0 (W y)))
  have hTrans := congrArg
    (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A (W y))
    (sphereSobolevInclusionL_trans (1/2 : ℝ) 0 (-(1/2 : ℝ)) (by norm_num) (by norm_num))
  exact hCancel.trans (hTrans.trans (hWG y))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_finiteFormalAdjointPhysical_L2
