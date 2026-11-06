import Calderon.ActualLowerUSAdjointZeroDerivative
import Calderon.ActualLowerUSFirstCoefficientGraph
import Calderon.ActualHigherSPhysicalPairing
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
Author: GPT-6.1 Sol. Before-code: ../zero-derivative-full-graph-upfront.md.
Upgrade of the actual finite pairing to its exact negative-space graph, using
explicit genuine finite test fields. No cap premise and no author compilation.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SphereHilbertDecomposition
  SpectralCoreRegularity ReferenceDensityBounds
  DirichletFamily.DriftBootstrap DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
  DirichletFamily.DriftBootstrap.ActualHigherSPhysicalPairing
  ActualModelCommutatorWords PrincipalCommutator
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)


variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

/-- Every actual harmonic singleton is the value of a genuine finite compact
smooth field, simultaneously at every Sobolev order. -/
private lemma exists_finiteCore_single_at (x : R3) (k : ℕ) (u : harmonicSphereSubspace k) :
    ∃ G : smoothCompactFiniteSphereCore hO hD, ∀ s : ℝ,
      finiteCoreSobolevLift hO hD s G x = sphereSobolevSingleL s k u := by
  let chi : ContDiffBump x := ⟨1,2,by norm_num,by norm_num⟩
  have hchi : chi x = 1 := chi.one_of_mem_closedBall (mem_closedBall_self (by norm_num))
  let G : smoothCompactFiniteSphereCore hO hD := ⟨fun y => chi y • (u : SphereL2),
    chi.contDiff.smul contDiff_const,chi.hasCompactSupport.smul_right,
    ⟨k+1,by
      intro y l hl
      change sphereHarmonicCoordinate hO hD l (chi y • (u : SphereL2)) = 0
      rw [map_smul,sphereHarmonicCoordinate_subtype_of_ne hO hD l k (by omega) u,smul_zero]⟩⟩
  have hValue : G.val x = (u : SphereL2) := by
    change chi x • (u : SphereL2) = _
    rw [hchi,one_smul]
  refine ⟨G,?_⟩
  intro s
  apply sphereSobolev_ext s
  intro l
  rw [sphereSobolevCoefficientL_finiteCoreSobolevLift,hValue]
  by_cases hl : l=k
  · subst l
    rw [sphereSobolevCoefficientL_single_self,sphereHarmonicCoordinate_apply,
      sphereHarmonicDecomposition_subtype]
    simp only [lp.single_apply_self]
  · rw [sphereHarmonicCoordinate_subtype_of_ne hO hD l k hl u,
      sphereSobolevCoefficientL_single_ne s k l hl]

private lemma negative_eq_of_finiteCore_pairings (x : R3) (A B : Neg)
    (h : ∀ G : smoothCompactFiniteSphereCore hO hD,
      PP (finiteCoreSobolevLift hO hD (1/2 : ℝ) G x) A =
      PP (finiteCoreSobolevLift hO hD (1/2 : ℝ) G x) B) : A = B := by
  let LA : Half →L[ℝ] ℝ := innerSL ℝ A
  let LB : Half →L[ℝ] ℝ := innerSL ℝ B
  have hAB : LA = LB := by
    apply sphereSobolev_clm_eq_of_single (1/2 : ℝ)
    intro k u
    obtain ⟨G,hG⟩ := exists_finiteCore_single_at hO hD x k u
    have hg := h G
    rw [hG (1/2 : ℝ)] at hg
    calc
      _ = PP (sphereSobolevSingleL (1/2 : ℝ) k u) A := real_inner_comm _ _
      _ = PP (sphereSobolevSingleL (1/2 : ℝ) k u) B := hg
      _ = _ := real_inner_comm _ _
  have hTest := congrArg (fun L : Half →L[ℝ] ℝ => L (A-B)) hAB
  simp only [LA,LB,innerSL_apply_apply] at hTest
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [inner_sub_left]
  exact sub_eq_zero.mpr hTest

private lemma finiteCore_half_negative_pairing
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    PP (finiteCoreSobolevLift hO hD (1/2 : ℝ) G x)
      (finiteCoreSobolevLift hO hD (-(1/2 : ℝ)) F x) = ⟪F.val x,G.val x⟫_ℝ := by
  have hp := finiteCore_halfPairing_eq_inner hO hD G
    (finiteCoreSobolevLift hO hD (1/2 : ℝ) F x) x
  rw [sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ) (by norm_num),
    sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num),
    halfToSphereL2_finiteCoreSobolevLift hO hD] at hp
  exact hp.trans (real_inner_comm _ _)

/-- The actual dJ representative equals the negative lift of the literal native
coefficient derivative. Its original Ceta beta cap can now be paired against
arbitrary Half vectors, including a nonfinite physical Pstar output. -/
theorem nativeULowerAdjointZeroDerivativeSobolev_negative_graph
    (hF : SphereFischerInner) (g g2 : MatrixField)
    (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (i : Fin 3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeULowerAdjointZeroDerivativeSobolev hO hD hF g g2 hg L q dr Ar p i x
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) =
    finiteCoreSobolevLift hO hD (-(1/2 : ℝ))
      (coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i))
        (nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr) F) x := by
  apply negative_eq_of_finiteCore_pairings hO hD x
  intro G
  exact (nativeULowerAdjointZeroDerivativeSobolev_finite_graph
    hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i F G x).trans
    (finiteCore_half_negative_pairing hO hD _ G x).symm

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
