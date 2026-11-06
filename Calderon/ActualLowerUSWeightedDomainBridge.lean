import Calderon.ActualLowerSWeakDomain
import Calderon.NativeCoreReferenceDensityIntegrationByParts
import Calderon.ActualFiniteHarmonicModelBAngularAdjoint
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
Exact weighted transpose on finite tests against unrestricted smooth SphereL2
fields, including the same original physical S output. No LA(S F) is formed.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace

namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualScalarPrincipalAdjoint ScalarBaseAdjoint ReferenceDensityBounds
  NormalizedPrincipalMetric PrincipalCommutator ConformalDepth

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hF : SphereFischerInner) (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
  (hg2 : IsAdmissibleMetric g2) (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)

local notation "FC" => smoothCompactFiniteSphereCore hO hD
local notation "mu" => (fun x : R3 => referenceDensityFamily g L (q,x))
local notation "dd" i:max => coreDirectionalDerivative hO hD (coordinateDirection i)
local notation "bb" i:max => nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr
local notation "cc" => nativeC hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
local notation "AF" => nativeUFirstZeroPart hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "LA" => nativeULowerAdjointCore hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "JJ" => nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr

include hg in
private lemma lowerWeightedDensity_smooth : ContDiff ℝ ∞ mu :=
  (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)

include hg in
private lemma lowerWeightedDensityInv_smooth : ContDiff ℝ ∞ (fun x => (mu x)⁻¹) :=
  (contDiff_referenceDensityFamily_inv g hg L).comp (contDiff_const.prodMk contDiff_id)

local notation "MM" => coreScalar hO hD mu (lowerWeightedDensity_smooth g hg L q)
local notation "MI" => coreScalar hO hD (fun x => (mu x)⁻¹)
  (lowerWeightedDensityInv_smooth g hg L q)

/-- Explicit full zero coefficient transpose, with the original density
inside every ordered B coefficient derivative. -/
def nativeULowerAdjointZeroWeightedTranspose : Module.End ℝ FC :=
  cc - MI * ∑ i : Fin 3,
    ActualModelCommutatorWords.coefficientDerivative (dd i) (MM * bb i)

local notation "JX" => nativeULowerAdjointZeroWeightedTranspose
  hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr

private lemma lowerWeightedDensity_mul_inv : MM * MI = (1 : Module.End ℝ FC) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  change mu x • ((mu x)⁻¹ • F.val x) = F.val x
  rw [smul_smul, mul_inv_cancel₀ (referenceDensityFamily_pos g hg L (q,x)).ne', one_smul]

private lemma lowerWeightedTranspose_ring {R : Type*} [Ring R]
    (M I C : R) (d b : Fin 3 → R) (hMI : M * I = 1) :
    M * ((∑ i : Fin 3, b i * d i) + C) =
      (∑ i : Fin 3, d i * M * b i) +
        M * (C - I * ∑ i : Fin 3, (d i * (M * b i) - (M * b i) * d i)) := by
  have hZero : M * (C - I * ∑ i : Fin 3, (d i * (M * b i) - (M * b i) * d i)) =
      M * C - ∑ i : Fin 3, (d i * (M * b i) - (M * b i) * d i) := by
    rw [mul_sub, ← mul_assoc, hMI, one_mul]
  rw [hZero, mul_add, Finset.mul_sum]
  simp only [Finset.sum_sub_distrib, ← mul_assoc]
  abel

/-- The new operator remains on the original smooth compact finite core. -/
theorem finiteCoreSupportPreserving_nativeULowerAdjointZeroWeightedTranspose :
    FiniteCoreSupportPreserving hO hD JX := by
  unfold nativeULowerAdjointZeroWeightedTranspose
  apply finiteCoreSupportPreserving_sub hO hD
  · exact finiteCoreSupportPreserving_nativeC hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
  · apply finiteCoreSupportPreserving_mul hO hD
    · exact finiteCoreSupportPreserving_coreScalar hO hD _ _
    · apply finiteCoreSupportPreserving_sum
      intro i _hi
      unfold ActualModelCommutatorWords.coefficientDerivative ActualModelCommutatorWords.commutator
      apply finiteCoreSupportPreserving_sub hO hD
      · apply finiteCoreSupportPreserving_mul hO hD
        · exact finiteCoreSupportPreserving_coreDirectionalDerivative hO hD _
        · exact finiteCoreSupportPreserving_mul hO hD _ _
            (finiteCoreSupportPreserving_coreScalar hO hD _ _)
            (finiteCoreSupportPreserving_nativeB hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i)
      · apply finiteCoreSupportPreserving_mul hO hD
        · exact finiteCoreSupportPreserving_mul hO hD _ _
            (finiteCoreSupportPreserving_coreScalar hO hD _ _)
            (finiteCoreSupportPreserving_nativeB hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i)
        · exact finiteCoreSupportPreserving_coreDirectionalDerivative hO hD _

/-- Exact finite test-vector identity. Its pairing is valid against ANY
SphereL2 value; it asserts no finite or classical LA output for that value. -/
theorem nativeULowerWeightedTranspose_eq :
    MM * AF = (∑ i : Fin 3, (dd i) * MM * (bb i)) + MM * JX := by
  simpa only [nativeUFirstZeroPart, nativeULowerAdjointZeroWeightedTranspose,
    ActualModelCommutatorWords.coefficientDerivative, ActualModelCommutatorWords.commutator]
    using (lowerWeightedTranspose_ring (R := Module.End ℝ FC) MM MI cc
      (fun i : Fin 3 => dd i) (fun i : Fin 3 => bb i)
      (lowerWeightedDensity_mul_inv hO hD g hg L q))

private lemma lowerCore_pair_integrable (F : FC) (H : R3 → SphereL2)
    (hH : Continuous H) : Integrable (fun x => ⟪F.val x,H x⟫_ℝ) := by
  simpa only [real_inner_comm] using BaseDensityAdjoint.compact_inner_integrable
    H F.val hH F.property.1.continuous F.property.2.1

include hg in
private lemma lowerWeightedCore_pair_integrable (F : FC) (H : R3 → SphereL2)
    (hH : Continuous H) : Integrable (fun x => mu x * ⟪F.val x,H x⟫_ℝ) := by
  have ht := lowerCore_pair_integrable hO hD (MM F) H hH
  simpa only [coreScalar, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk,
    real_inner_smul_left] using ht

private lemma lowerCore_full_field_Green (i : Fin 3) (V : FC)
    (H : R3 → SphereL2) (hH : ContDiff ℝ ∞ H) :
    (∫ x, ⟪((dd i) V).val x,H x⟫_ℝ) =
      -(∫ x, ⟪V.val x,directionalFDeriv (coordinateDirection i) H x⟫_ℝ) := by
  have ht := BaseDensityAdjoint.compact_inner_directionalDeriv (coordinateDirection i)
    H V.val hH V.property.1 V.property.2.1
  change (∫ x, ⟪H x,directionalFDeriv (coordinateDirection i) V.val x⟫_ℝ) =
    -(∫ x, ⟪directionalFDeriv (coordinateDirection i) H x,V.val x⟫_ℝ) at ht
  calc
    _ = ∫ x, ⟪H x,directionalFDeriv (coordinateDirection i) V.val x⟫_ℝ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        change ⟪directionalFDeriv (coordinateDirection i) V.val x,H x⟫_ℝ = _
        exact real_inner_comm _ _)
    _ = -(∫ x, ⟪directionalFDeriv (coordinateDirection i) H x,V.val x⟫_ℝ) := ht
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => real_inner_comm _ _)

/-- The finite transpose test vector agrees with the literal physical A pairing. -/
theorem nativeULowerWeightedTranspose_pairing (F : FC) (H : R3 → SphereL2) (x : R3) :
    mu x * ⟪(AF F).val x,H x⟫_ℝ =
      (∑ i : Fin 3, ⟪((dd i) (MM ((bb i) F))).val x,H x⟫_ℝ) +
        mu x * ⟪(JX F).val x,H x⟫_ℝ := by
  have he := congrArg (fun T : Module.End ℝ FC => ⟪(T F).val x,H x⟫_ℝ)
    (nativeULowerWeightedTranspose_eq hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr)
  simpa only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sum_apply,
    Submodule.coe_add, Submodule.coe_sum, Pi.add_apply, Finset.sum_apply,
    inner_add_left, sum_inner, coreScalar, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_mk, real_inner_smul_left] using he

/-- Genuine full-Hilbert-field base Green, with every derivative of the
original density retained in JX. Only finite tests require compact support. -/
theorem nativeULower_full_field_Green (F : FC) (H : R3 → SphereL2)
    (hH : ContDiff ℝ ∞ H) :
    Integrable (fun x => mu x * ⟪(AF F).val x,H x⟫_ℝ) ∧
    (∀ i : Fin 3, Integrable (fun x => mu x *
      ⟪((bb i) F).val x,directionalFDeriv (coordinateDirection i) H x⟫_ℝ)) ∧
    Integrable (fun x => mu x * ⟪(JX F).val x,H x⟫_ℝ) ∧
    (∫ x, mu x * ⟪(AF F).val x,H x⟫_ℝ) =
      -(∑ i : Fin 3, ∫ x, mu x *
        ⟪((bb i) F).val x,directionalFDeriv (coordinateDirection i) H x⟫_ℝ) +
      ∫ x, mu x * ⟪(JX F).val x,H x⟫_ℝ := by
  have hA := lowerWeightedCore_pair_integrable hO hD g hg L q (AF F) H hH.continuous
  have hB (i : Fin 3) := lowerWeightedCore_pair_integrable hO hD g hg L q ((bb i) F)
    (directionalFDeriv (coordinateDirection i) H)
    (contDiff_directionalFDeriv (coordinateDirection i) H hH).continuous
  have hJ := lowerWeightedCore_pair_integrable hO hD g hg L q (JX F) H hH.continuous
  have hDerivInt (i : Fin 3) := lowerCore_pair_integrable hO hD
    ((dd i) (MM ((bb i) F))) H hH.continuous
  have hGreen (i : Fin 3) :
      (∫ x, ⟪((dd i) (MM ((bb i) F))).val x,H x⟫_ℝ) =
        -(∫ x, mu x *
          ⟪((bb i) F).val x,directionalFDeriv (coordinateDirection i) H x⟫_ℝ) := by
    calc
      _ = -(∫ x, ⟪(MM ((bb i) F)).val x,
          directionalFDeriv (coordinateDirection i) H x⟫_ℝ) :=
        lowerCore_full_field_Green hO hD i (MM ((bb i) F)) H hH
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by
          change ⟪mu x • ((bb i) F).val x,
            directionalFDeriv (coordinateDirection i) H x⟫_ℝ = _
          exact real_inner_smul_left _ _ _)
  refine ⟨hA,hB,hJ,?_⟩
  calc
    _ = ∫ x, (∑ i : Fin 3, ⟪((dd i) (MM ((bb i) F))).val x,H x⟫_ℝ) +
        mu x * ⟪(JX F).val x,H x⟫_ℝ := by
      apply integral_congr_ae
      exact Eventually.of_forall (nativeULowerWeightedTranspose_pairing
        hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F H)
    _ = (∑ i : Fin 3, ∫ x, ⟪((dd i) (MM ((bb i) F))).val x,H x⟫_ℝ) +
        ∫ x, mu x * ⟪(JX F).val x,H x⟫_ℝ := by
      rw [integral_add (integrable_finsetSum _ (fun i _ => hDerivInt i)) hJ,
        integral_finsetSum _ (fun i _ => hDerivInt i)]
    _ = _ := by simp only [hGreen, Finset.sum_neg_distrib]

/-! The next finite identities recover the zero coefficient's genuine angular
adjoint, without assuming any new analytic estimate or full-output domain. -/

/-- Full native U adjunction minus its exact scalar adjunction. -/
theorem nativeULower_integrated_adjoint (F G : FC) :
    (∫ x, mu x * ⟪(AF F).val x,G.val x⟫_ℝ) =
      ∫ x, mu x * ⟪F.val x,(LA G).val x⟫_ℝ := by
  let PP : Module.End ℝ FC := nativeScalarPrincipalPart hO hD g g2 hg hg2
    L q dr Ar p hdr hAr
  let UD : Module.End ℝ FC := nativeUdag hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
  let PD : Module.End ℝ FC := UD - LA
  let aa := actualPrincipalMatrix g L q dr Ar p
    (referenceNormalizedPrincipalDifference g g2 L q)
  have hPP (V : FC) (x : R3) :
      (PP V).val x = scalarSecondBase coordinateDirection aa V.val x :=
    nativeScalarPrincipalPart_apply_eq_scalarSecondBase hO hD g g2 hg hg2
      L q dr Ar p hdr hAr V x
  have hPD (V : FC) (x : R3) :
      (PD V).val x = scalarSecondBaseAdjoint coordinateDirection mu aa V.val x := by
    change (UD V).val x - (LA V).val x = _
    rw [nativeULowerAdjointCore_apply,
      nativeUdag_apply_eq_scalarAdjoint_add_firstZero hO hD hF g g2 hg hg2
        L q dr Ar p hdr hAr V x]
    abel
  have ha (i j : Fin 3) : ContDiff ℝ ∞ (fun x => aa x i j) := by
    exact ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L q dr Ar p
      (referenceNormalizedPrincipalDifference g g2 L q) hdr hAr
      (fun i j => NormalizedPrincipalMetricSmooth.contDiff_referenceNormalizedPrincipalDifference_entry
        g g2 hg hg2 L q i j) i j
  have hs := compact_scalarSecondBase_adjoint coordinateDirection mu aa F.val G.val
    (lowerWeightedDensity_smooth g hg L q) ha F.property.1 G.property.1 F.property.2.1
    (fun x => referenceDensityFamily_pos g hg L (q,x))
  have hScalar : (∫ x, mu x * ⟪(PP F).val x,G.val x⟫_ℝ) =
      ∫ x, mu x * ⟪F.val x,(PD G).val x⟫_ℝ := by
    simpa only [hPP,hPD] using hs
  have hP := lowerWeightedCore_pair_integrable hO hD g hg L q (PP F) G.val G.property.1.continuous
  have hA := lowerWeightedCore_pair_integrable hO hD g hg L q (AF F) G.val G.property.1.continuous
  have hPd := lowerWeightedCore_pair_integrable hO hD g hg L q F (PD G).val (PD G).property.1.continuous
  have hLa := lowerWeightedCore_pair_integrable hO hD g hg L q F (LA G).val (LA G).property.1.continuous
  have hU := compact_nativeU_adjoint hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr F G
  have hForward : nativeU hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr = PP + AF :=
    nativeU_eq_scalarPrincipal_add_firstZero hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
  have hReverse : nativeUdag hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr = PD + LA := by
    change UD = (UD-LA)+LA
    abel
  rw [hForward,hReverse] at hU
  simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply,
    inner_add_left, inner_add_right, mul_add] at hU
  rw [integral_add hP hA, integral_add hPd hLa] at hU
  linarith

private lemma lowerFirst_sphere_pairing (i : Fin 3) (F G : FC) (x : R3) :
    ⟪(nativeULowerAdjointFirstCoefficient hO hD hF g g2 hg hg2
      L q dr Ar p hdr hAr i F).val x,G.val x⟫_ℝ =
      -⟪F.val x,((bb i) G).val x⟫_ℝ := by
  have hDcoef : nativeULowerAdjointFirstCoefficient hO hD hF g g2 hg hg2
      L q dr Ar p hdr hAr i =
      -nativeBAngularAdjoint hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr := by
    unfold nativeULowerAdjointFirstCoefficient nativeBAngularAdjoint
    abel
  rw [hDcoef]
  simp only [LinearMap.neg_apply,Submodule.coe_neg,Pi.neg_apply,inner_neg_left]
  congr 1
  calc
    _ = ⟪G.val x,(nativeBAngularAdjoint hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr F).val x⟫_ℝ :=
      real_inner_comm _ _
    _ = ⟪((bb i) G).val x,F.val x⟫_ℝ :=
      (nativeB_pointwise_inner_adjoint hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr G F x).symm
    _ = _ := real_inner_comm _ _

/-- The literal J=C+W-a0 has exactly the integrated sphere adjunction of the
explicit weighted B-divergence transpose. All original coefficients survive. -/
theorem nativeULowerAdjointZeroWeightedTranspose_integrated (F G : FC) :
    (∫ x, mu x * ⟪(JJ F).val x,G.val x⟫_ℝ) =
      ∫ x, mu x * ⟪F.val x,(JX G).val x⟫_ℝ := by
  have hLower := nativeULower_integrated_adjoint hO hD hF g g2 hg hg2
    L q dr Ar p hdr hAr G F
  have hGreen := nativeULower_full_field_Green hO hD hF g g2 hg hg2
    L q dr Ar p hdr hAr G F.val F.property.1
  have hJ := lowerWeightedCore_pair_integrable hO hD g hg L q (JJ F) G.val G.property.1.continuous
  have hB (i : Fin 3) := lowerWeightedCore_pair_integrable hO hD g hg L q ((bb i) G)
    (directionalFDeriv (coordinateDirection i) F.val)
    (contDiff_directionalFDeriv (coordinateDirection i) F.val F.property.1).continuous
  have hPoint (x : R3) : mu x * ⟪G.val x,(LA F).val x⟫_ℝ =
      -(∑ i : Fin 3, mu x * ⟪((bb i) G).val x,
        directionalFDeriv (coordinateDirection i) F.val x⟫_ℝ) +
      mu x * ⟪(JJ F).val x,G.val x⟫_ℝ := by
    rw [← real_inner_comm (G.val x) ((LA F).val x)]
    simp only [nativeULowerAdjointCore, ActualModelCommutatorWords.modelFirstOrder,
      LinearMap.add_apply,LinearMap.sum_apply,Module.End.mul_apply,
      Submodule.coe_add,Submodule.coe_sum,Pi.add_apply,Finset.sum_apply,
      inner_add_left,sum_inner,mul_add,Finset.mul_sum]
    simp_rw [lowerFirst_sphere_pairing hO hD hF g g2 hg hg2
      L q dr Ar p hdr hAr]
    simp only [coreDirectionalDerivative,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,
      mul_neg,Finset.sum_neg_distrib,real_inner_comm]
  have hExpand : (∫ x, mu x * ⟪G.val x,(LA F).val x⟫_ℝ) =
      -(∑ i : Fin 3, ∫ x, mu x * ⟪((bb i) G).val x,
        directionalFDeriv (coordinateDirection i) F.val x⟫_ℝ) +
      ∫ x, mu x * ⟪(JJ F).val x,G.val x⟫_ℝ := by
    have hSumInt : Integrable (fun x => ∑ i : Fin 3, mu x *
        ⟪((bb i) G).val x,directionalFDeriv (coordinateDirection i) F.val x⟫_ℝ) :=
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => hB i)
    have hSum : (∫ x, ∑ i : Fin 3, mu x *
        ⟪((bb i) G).val x,directionalFDeriv (coordinateDirection i) F.val x⟫_ℝ) =
        ∑ i : Fin 3, ∫ x, mu x *
          ⟪((bb i) G).val x,directionalFDeriv (coordinateDirection i) F.val x⟫_ℝ :=
      integral_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => hB i)
    calc
      _ = ∫ x, -(∑ i : Fin 3, mu x * ⟪((bb i) G).val x,
          directionalFDeriv (coordinateDirection i) F.val x⟫_ℝ) +
          mu x * ⟪(JJ F).val x,G.val x⟫_ℝ :=
        integral_congr_ae (Eventually.of_forall hPoint)
      _ = (∫ x, -(∑ i : Fin 3, mu x * ⟪((bb i) G).val x,
          directionalFDeriv (coordinateDirection i) F.val x⟫_ℝ)) +
          ∫ x, mu x * ⟪(JJ F).val x,G.val x⟫_ℝ :=
        integral_add hSumInt.neg hJ
      _ = -(∫ x, ∑ i : Fin 3, mu x * ⟪((bb i) G).val x,
          directionalFDeriv (coordinateDirection i) F.val x⟫_ℝ) +
          ∫ x, mu x * ⟪(JJ F).val x,G.val x⟫_ℝ := by
        exact congrArg (fun z : ℝ => z + ∫ x, mu x * ⟪(JJ F).val x,G.val x⟫_ℝ)
          (integral_neg _)
      _ = _ := congrArg (fun z : ℝ => -z + ∫ x, mu x * ⟪(JJ F).val x,G.val x⟫_ℝ) hSum
  have hEq := hLower.symm.trans hGreen.2.2.2
  rw [hExpand] at hEq
  have hSwap : (∫ x, mu x * ⟪(JX G).val x,F.val x⟫_ℝ) =
      ∫ x, mu x * ⟪F.val x,(JX G).val x⟫_ℝ := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      change mu x * ⟪(JX G).val x,F.val x⟫_ℝ = mu x * ⟪F.val x,(JX G).val x⟫_ℝ
      exact congrArg (fun z : ℝ => mu x * z) (real_inner_comm (F.val x) ((JX G).val x)))
  linarith

/-- Internal finite-witness uniqueness: any `Js` satisfying the pointwise adjoint
identity `hJs` is the weighted transpose. -/
theorem nativeULowerAdjointZeroWeightedTranspose_eq_of_sphere_adjoint
    (Js : Module.End ℝ FC)
    (hJs : ∀ F G : FC, ∀ x : R3,
      ⟪(JJ F).val x,G.val x⟫_ℝ = ⟪F.val x,(Js G).val x⟫_ℝ) : Js = JX := by
  apply LinearMap.ext
  intro G
  let R : FC := (Js-JX) G
  have hPair := nativeULowerAdjointZeroWeightedTranspose_integrated
    hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr R G
  have hPair' : (∫ x, mu x * ⟪R.val x,(Js G).val x⟫_ℝ) =
      ∫ x, mu x * ⟪R.val x,(JX G).val x⟫_ℝ := by
    simpa only [hJs] using hPair
  have hI1 := lowerWeightedCore_pair_integrable hO hD g hg L q R (Js G).val (Js G).property.1.continuous
  have hI2 := lowerWeightedCore_pair_integrable hO hD g hg L q R (JX G).val (JX G).property.1.continuous
  have hZero : (∫ x, mu x * ⟪R.val x,R.val x⟫_ℝ) = 0 := by
    calc
      _ = (∫ x, mu x * ⟪R.val x,(Js G).val x⟫_ℝ) -
          ∫ x, mu x * ⟪R.val x,(JX G).val x⟫_ℝ := by
        rw [← integral_sub hI1 hI2]
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by
          change mu x * ⟪R.val x,(Js G).val x-(JX G).val x⟫_ℝ = _
          rw [inner_sub_right,mul_sub])
      _ = 0 := sub_eq_zero.mpr hPair'
  have hInt := lowerWeightedCore_pair_integrable hO hD g hg L q R R.val R.property.1.continuous
  have hNonneg (x : R3) : 0 ≤ mu x * ⟪R.val x,R.val x⟫_ℝ :=
    mul_nonneg (referenceDensityFamily_pos g hg L (q,x)).le real_inner_self_nonneg
  have hAE : (fun x => mu x * ⟪R.val x,R.val x⟫_ℝ) =ᵐ[volume] (fun _ => (0 : ℝ)) :=
    (integral_eq_zero_iff_of_nonneg hNonneg hInt).mp hZero
  have hEvery : (fun x => mu x * ⟪R.val x,R.val x⟫_ℝ) = (fun _ => (0 : ℝ)) :=
    MeasureTheory.Measure.eq_of_ae_eq hAE
      ((lowerWeightedDensity_smooth g hg L q).continuous.mul
        (R.property.1.continuous.inner R.property.1.continuous)) continuous_const
  apply Subtype.ext
  funext x
  have hz := congrFun hEvery x
  have hInner : ⟪R.val x,R.val x⟫_ℝ = 0 :=
    (mul_eq_zero.mp hz).resolve_left (referenceDensityFamily_pos g hg L (q,x)).ne'
  have hR : R.val x = 0 := inner_self_eq_zero.mp hInner
  apply sub_eq_zero.mp
  exact hR

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSWeightedDomainBridge
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualModelSMixedComparison ActualAngularHighDraft ConformalDepth
  ReferenceWeightedApproximation ReferenceDensityBounds NormalizedPrincipalMetric PrincipalCommutator

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
  (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
  (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)

local notation "mu" => (fun x : R3 => referenceDensityFamily g L (q,x))
local notation "SO" => ActualHigherSFormation.nativeHigherSOut
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
  dr Ar p hdr hAr q hreg data.δ0 data.germs g2
local notation "LA" => nativeULowerAdjointCore hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "JX" => nativeULowerAdjointZeroWeightedTranspose hO hD hF g g2 hg hg2
  L q dr Ar p hdr hAr
local notation "bb" i:max => nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr
local notation "Lo" => nativeULowerSCrossDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
  g2 hg2 dr Ar p hdr hAr q
local notation "CRoom" δ:max => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "Tq" => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)

/-- The signed lower U/S integral in genuine full-output Green form. The same
common room derives all S smoothness; no finite-output premise is introduced. -/
theorem actual_lower_S_full_Green_of_common_room
    (δ : ℝ) (Cm : CRoom δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (hq : q ∈ Icc (0 : ℝ) 1) (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, Tq x ∈ ParamRoom δ) :
    Integrable (fun x => mu x * Lo F x) ∧
    (∀ i : Fin 3, Integrable (fun x => mu x *
      ⟪((bb i) F).val x,directionalFDeriv (coordinateDirection i) (SO F) x⟫_ℝ)) ∧
    Integrable (fun x => mu x * ⟪(JX F).val x,SO F x⟫_ℝ) ∧
    Integrable (fun x => mu x * ⟪F.val x,SO (LA F) x⟫_ℝ) ∧
    (∫ x, mu x * Lo F x) =
      -(∑ i : Fin 3, ∫ x, mu x *
        ⟪((bb i) F).val x,directionalFDeriv (coordinateDirection i) (SO F) x⟫_ℝ) +
      (∫ x, mu x * ⟪(JX F).val x,SO F x⟫_ℝ) -
      ∫ x, mu x * ⟪F.val x,SO (LA F) x⟫_ℝ := by
  have hFormation := ActualCommonQuadraticFormationConsumer.higherSOutputConclusions_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq F hTF
  have hSmooth : ContDiff ℝ ∞ (SO F) := hFormation.2.2.2.2.2.1.1
  have hG := nativeULower_full_field_Green hO hD hF g g2 hg hg2
    L q dr Ar p hdr hAr F (SO F) hSmooth
  have hWeak := ActualLowerSWeakDomain.actualLowerSWeakIdentity_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data g2 hg2 dr Ar p hdr hAr q δ Cm F hTF
  have hAd := ActualLowerUSAdjointCore.actual_lower_adjoint_S_weak_identity_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data g2 hg2 dr Ar p hdr hAr q δ Cm F hTF
  have hSplit := weighted_difference_integral mu
    (fun x => ⟪(nativeUFirstZeroPart hO hD hF g g2 hg hg2
      L q dr Ar p hdr hAr F).val x,SO F x⟫_ℝ)
    (fun x => ⟪F.val x,SO (LA F) x⟫_ℝ) hG.1 hAd.2.1
  refine ⟨hWeak.1,hG.2.1,hG.2.2.1,hAd.2.1,?_⟩
  calc
    _ = ∫ x, mu x * ActualLowerSWeakDomain.actualLowerSWeakDensity
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data g2 hg2 dr Ar p hdr hAr q F x := hWeak.2.2.2.1
    _ = _ := by
      change (∫ x, mu x * (⟪(nativeUFirstZeroPart hO hD hF g g2 hg hg2
        L q dr Ar p hdr hAr F).val x,SO F x⟫_ℝ - ⟪F.val x,SO (LA F) x⟫_ℝ)) = _
      rw [hSplit.2,hG.2.2.2]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSWeightedDomainBridge
