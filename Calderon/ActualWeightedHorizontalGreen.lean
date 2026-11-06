import Calderon.BaseDensityAdjoint
import Calderon.ReferenceDensityBounds
import Calderon.NativeCoreReferenceDensityIntegrationByParts
import Calderon.ActualHorizontalSobolevConnection
import Calderon.ActualWeightedHorizontalActions
import Calderon.SphereSobolevPairing
import Calderon.SphereSobolevHalfDualRotationPairing
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! Before-source: output/WEIGHTED-GREEN-MATHEMATICS.md.
Actual R3 weighted horizontal Green identity for arbitrary smooth full-output fields
(`v` compactly supported), proved from the generic compact Hilbert API `BaseDensityAdjoint`. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ContDiff ENNReal

/-! ### Generic coordinate and frame Green (any real Hilbert space) -/
namespace OAI.AnisotropicCalderon.WeightedFrameGreen
open PrincipalCommutator ReferenceDensityBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The weighted frame divergence `Σ_j D_{e_j}(rho · X_j)` (density kept inside the derivative). -/
def weightedFrameDivergence (rho : R3 → ℝ) (X : R3 → R3) (y : R3) : ℝ :=
  ∑ j : Fin 3, BaseDensityAdjoint.directionalDeriv (coordinateDirection j)
    (fun z => rho z * X z j) y

lemma integrable_of_continuous_of_vanishing {F : Type*} [NormedAddCommGroup F]
    {h : R3 → ℝ} {G : R3 → F} (hh : Continuous h) (hG : HasCompactSupport G)
    (hv : ∀ y, G y = 0 → h y = 0) : Integrable h := by
  apply hh.integrable_of_hasCompactSupport
  apply hG.mono
  intro y hy
  simp only [Function.mem_support] at hy ⊢
  exact fun h0 => hy (hv y h0)

lemma coordinateDirection_eq_single (j : Fin 3) :
    coordinateDirection j = EuclideanSpace.single j (1 : ℝ) := by
  first
  | rfl
  | simp [coordinateDirection]
  | (ext k; simp [coordinateDirection, EuclideanSpace.single_apply])

lemma vector_eq_sum_coordinate (x : R3) :
    x = ∑ j : Fin 3, x j • coordinateDirection j := by
  have h := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at h
  simp only [coordinateDirection_eq_single]
  exact h.symm

lemma fderiv_apply_eq_sum_coordinate (u : R3 → E) (y X : R3) :
    fderiv ℝ u y X =
      ∑ j : Fin 3, X j • BaseDensityAdjoint.directionalDeriv (coordinateDirection j) u y := by
  calc fderiv ℝ u y X = fderiv ℝ u y (∑ j : Fin 3, X j • coordinateDirection j) :=
        congrArg (fun w : R3 => fderiv ℝ u y w) (vector_eq_sum_coordinate X)
    _ = ∑ j : Fin 3, X j • fderiv ℝ u y (coordinateDirection j) := by
        rw [map_sum]; simp only [map_smul]
    _ = _ := rfl

/-- Step 1: one fixed direction, scalar weight `mu` kept inside the derivative. -/
theorem compact_weighted_coordinate_green (e : R3) (mu : R3 → ℝ) (f g : R3 → E)
    (hmu : ContDiff ℝ ∞ mu) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) :
    (∫ y, mu y * ⟪BaseDensityAdjoint.directionalDeriv e g y, f y⟫_ℝ) =
      -(∫ y, mu y * ⟪g y, BaseDensityAdjoint.directionalDeriv e f y⟫_ℝ) -
        ∫ y, BaseDensityAdjoint.directionalDeriv e mu y * ⟪g y, f y⟫_ℝ := by
  have h := BaseDensityAdjoint.compact_weighted_first_adjoint e mu (fun _ => (1 : ℝ)) g f
    hmu contDiff_const hg hf hc
  simp only [mul_one] at h
  have hE (y : R3) :
      ⟪BaseDensityAdjoint.directionalDeriv e (fun z => mu z • f z) y, g y⟫_ℝ =
        mu y * ⟪g y, BaseDensityAdjoint.directionalDeriv e f y⟫_ℝ +
          BaseDensityAdjoint.directionalDeriv e mu y * ⟪g y, f y⟫_ℝ := by
    rw [BaseDensityAdjoint.directionalDeriv_smul e mu f hmu hf y, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_comm (g y) (f y),
      real_inner_comm (g y) (BaseDensityAdjoint.directionalDeriv e f y)]
    ring
  have iA : Integrable (fun y => mu y * ⟪g y, BaseDensityAdjoint.directionalDeriv e f y⟫_ℝ) :=
    integrable_of_continuous_of_vanishing
      (hmu.continuous.mul (hg.continuous.inner
        (BaseDensityAdjoint.contDiff_directionalDeriv e f hf).continuous))
      hc (fun y hy => by simp [hy])
  have iB : Integrable
      (fun y => BaseDensityAdjoint.directionalDeriv e mu y * ⟪g y, f y⟫_ℝ) :=
    integrable_of_continuous_of_vanishing
      ((BaseDensityAdjoint.contDiff_directionalDeriv e mu hmu).continuous.mul
        (hg.continuous.inner hf.continuous))
      hc (fun y hy => by simp [hy])
  calc (∫ y, mu y * ⟪BaseDensityAdjoint.directionalDeriv e g y, f y⟫_ℝ)
      = -(∫ y, ⟪BaseDensityAdjoint.directionalDeriv e (fun z => mu z • f z) y, g y⟫_ℝ) := h
    _ = -(∫ y, (mu y * ⟪g y, BaseDensityAdjoint.directionalDeriv e f y⟫_ℝ +
          BaseDensityAdjoint.directionalDeriv e mu y * ⟪g y, f y⟫_ℝ)) := by
        congr 1; congr 1; funext y; exact hE y
    _ = _ := by rw [integral_add iA iB]; ring

/-- Step 2: smooth frame `X = Σ_j X_j e_j`, density inside the divergence. -/
theorem compact_weighted_frame_green (rho : R3 → ℝ) (X : R3 → R3) (f g : R3 → E)
    (hrho : ContDiff ℝ ∞ rho) (hX : ContDiff ℝ ∞ X) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    (∫ y, rho y * ⟪fderiv ℝ g y (X y), f y⟫_ℝ) =
      -(∫ y, rho y * ⟪g y, fderiv ℝ f y (X y)⟫_ℝ) -
        ∫ y, weightedFrameDivergence rho X y * ⟪g y, f y⟫_ℝ := by
  have hXj (j : Fin 3) : ContDiff ℝ ∞ (fun y => X y j) := (contDiff_piLp 2).1 hX j
  have hmu (j : Fin 3) : ContDiff ℝ ∞ (fun y => rho y * X y j) := hrho.mul (hXj j)
  have hj (j : Fin 3) :
      (∫ y, rho y * X y j *
        ⟪BaseDensityAdjoint.directionalDeriv (coordinateDirection j) g y, f y⟫_ℝ) =
      -(∫ y, rho y * X y j *
        ⟪g y, BaseDensityAdjoint.directionalDeriv (coordinateDirection j) f y⟫_ℝ) -
        ∫ y, BaseDensityAdjoint.directionalDeriv (coordinateDirection j)
          (fun z => rho z * X z j) y * ⟪g y, f y⟫_ℝ :=
    compact_weighted_coordinate_green (coordinateDirection j) (fun y => rho y * X y j) f g
      (hmu j) hf hg hc
  have iC (j : Fin 3) : Integrable (fun y => rho y * X y j *
      ⟪BaseDensityAdjoint.directionalDeriv (coordinateDirection j) g y, f y⟫_ℝ) :=
    integrable_of_continuous_of_vanishing
      ((hmu j).continuous.mul
        ((BaseDensityAdjoint.contDiff_directionalDeriv _ g hg).continuous.inner hf.continuous))
      (BaseDensityAdjoint.hasCompactSupport_directionalDeriv (coordinateDirection j) g hc)
      (fun y hy => by simp [hy])
  have iA (j : Fin 3) : Integrable (fun y => rho y * X y j *
      ⟪g y, BaseDensityAdjoint.directionalDeriv (coordinateDirection j) f y⟫_ℝ) :=
    integrable_of_continuous_of_vanishing
      ((hmu j).continuous.mul
        (hg.continuous.inner (BaseDensityAdjoint.contDiff_directionalDeriv _ f hf).continuous))
      hc (fun y hy => by simp [hy])
  have iB (j : Fin 3) : Integrable (fun y => BaseDensityAdjoint.directionalDeriv
      (coordinateDirection j) (fun z => rho z * X z j) y * ⟪g y, f y⟫_ℝ) :=
    integrable_of_continuous_of_vanishing
      ((BaseDensityAdjoint.contDiff_directionalDeriv _ _ (hmu j)).continuous.mul
        (hg.continuous.inner hf.continuous))
      hc (fun y hy => by simp [hy])
  have hL : (fun y => rho y * ⟪fderiv ℝ g y (X y), f y⟫_ℝ) = fun y => ∑ j : Fin 3,
      rho y * X y j *
        ⟪BaseDensityAdjoint.directionalDeriv (coordinateDirection j) g y, f y⟫_ℝ := by
    funext y
    rw [fderiv_apply_eq_sum_coordinate g y (X y), sum_inner, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_smul_left]
    ring
  have hR1 : (fun y => rho y * ⟪g y, fderiv ℝ f y (X y)⟫_ℝ) = fun y => ∑ j : Fin 3,
      rho y * X y j *
        ⟪g y, BaseDensityAdjoint.directionalDeriv (coordinateDirection j) f y⟫_ℝ := by
    funext y
    rw [fderiv_apply_eq_sum_coordinate f y (X y), inner_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_smul_right]
    ring
  have hR2 : (fun y => weightedFrameDivergence rho X y * ⟪g y, f y⟫_ℝ) = fun y =>
      ∑ j : Fin 3, BaseDensityAdjoint.directionalDeriv (coordinateDirection j)
        (fun z => rho z * X z j) y * ⟪g y, f y⟫_ℝ := by
    funext y
    unfold weightedFrameDivergence
    rw [Finset.sum_mul]
  rw [hL, hR1, hR2, integral_finsetSum _ (fun j _ => iC j),
    integral_finsetSum _ (fun j _ => iA j), integral_finsetSum _ (fun j _ => iB j),
    Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_sub_distrib, Finset.sum_neg_distrib]

end OAI.AnisotropicCalderon.WeightedFrameGreen

/-! ### Actual horizontal pairing algebra and the actual weighted Green identity -/
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds
  PrincipalCommutator WeightedFrameGreen

private lemma integrable_of_vanishing_on_compact_support {F : Type*} [Zero F]
    {h : R3 → ℝ} {G : R3 → F} (hh : Continuous h) (hG : HasCompactSupport G)
    (hv : ∀ y, G y = 0 → h y = 0) : Integrable h := by
  apply hh.integrable_of_hasCompactSupport
  apply hG.mono
  intro y hy
  simp only [Function.mem_support] at hy ⊢
  exact fun h0 => hy (hv y h0)

local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "DH" => sphereSobolevShiftedDegreeL (3/2 : ℝ)
local notation "DL" => sphereSobolevShiftedDegreeL (1/2 : ℝ)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)

/-- `J ∘ I` into the common normalized storage of order `1/2`. -/
def weightedGreenHighToHalf : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num))

local notation "KH" => weightedGreenHighToHalf

lemma halfPairing_add_right (a : SphereSobolev (1/2 : ℝ)) (b c : SphereSobolev (-(1/2 : ℝ))) :
    PP a (b + c) = PP a b + PP a c := by
  unfold sphereSobolevDualPairing; exact inner_add_right a b c

lemma halfPairing_smul_right (a : SphereSobolev (1/2 : ℝ)) (r : ℝ)
    (b : SphereSobolev (-(1/2 : ℝ))) : PP a (r • b) = r * PP a b := by
  unfold sphereSobolevDualPairing; exact real_inner_smul_right a b r

lemma halfPairing_sum_right {ι : Type*} (s : Finset ι) (a : SphereSobolev (1/2 : ℝ))
    (F : ι → SphereSobolev (-(1/2 : ℝ))) : PP a (∑ j ∈ s, F j) = ∑ j ∈ s, PP a (F j) := by
  unfold sphereSobolevDualPairing; exact inner_sum s F a

lemma halfPairing_zero_left (b : SphereSobolev (-(1/2 : ℝ))) : PP 0 b = 0 := by
  unfold sphereSobolevDualPairing; exact inner_zero_left b

lemma continuous_halfPairing {a : R3 → SphereSobolev (1/2 : ℝ)}
    {b : R3 → SphereSobolev (-(1/2 : ℝ))} (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun y => PP (a y) (b y)) := by
  unfold sphereSobolevDualPairing; exact ha.inner hb

/-- (S) The half/negative pairing through `J` is symmetric. -/
lemma halfPairing_inclusion_symm (a b : SphereSobolev (1/2 : ℝ)) :
    PP a (JL b) = PP b (JL a) := by
  rw [sphereSobolevDualPairing_eq_tsum, sphereSobolevDualPairing_eq_tsum]
  apply tsum_congr
  intro k
  rw [sphereSobolevCoefficientL_inclusion, sphereSobolevCoefficientL_inclusion]
  exact real_inner_comm _ _

/-- (K) The exact physical degree `k` (including `k = 0`) is pairing-symmetric. -/
lemma halfPairing_degree_symm (a b : SphereSobolev (1/2 : ℝ)) :
    PP a (DL b) = PP b (DL a) := by
  have hc (x : SphereSobolev (1/2 : ℝ)) (k : ℕ) :
      sphereSobolevCoefficientL (-(1/2 : ℝ)) k (DL x) =
        (k : ℝ) • sphereSobolevCoefficientL (1/2 : ℝ) k x := by
    have hOrder : sphereSobolevCoefficientL (-(1/2 : ℝ)) k (DL x) =
        sphereSobolevCoefficientL ((1/2 : ℝ) - 1) k (DL x) :=
      congrArg (fun s : ℝ => sphereSobolevCoefficientL s k (DL x))
        (by norm_num : (-(1/2 : ℝ)) = (1/2 : ℝ) - 1)
    exact hOrder.trans (sphereSobolevCoefficientL_shiftedDegree (1/2 : ℝ) k x)
  rw [sphereSobolevDualPairing_eq_tsum, sphereSobolevDualPairing_eq_tsum]
  apply tsum_congr
  intro k
  rw [hc b k, hc a k]
  have hLeft := real_inner_smul_right (F := harmonicSphereSubspace k)
    (sphereSobolevCoefficientL (1/2 : ℝ) k a) (sphereSobolevCoefficientL (1/2 : ℝ) k b) (k : ℝ)
  have hRight := real_inner_smul_right (F := harmonicSphereSubspace k)
    (sphereSobolevCoefficientL (1/2 : ℝ) k b) (sphereSobolevCoefficientL (1/2 : ℝ) k a) (k : ℝ)
  have hComm :
      ⟪sphereSobolevCoefficientL (1/2 : ℝ) k a,sphereSobolevCoefficientL (1/2 : ℝ) k b⟫_ℝ =
        ⟪sphereSobolevCoefficientL (1/2 : ℝ) k b,sphereSobolevCoefficientL (1/2 : ℝ) k a⟫_ℝ :=
    (real_inner_comm (sphereSobolevCoefficientL (1/2 : ℝ) k a)
      (sphereSobolevCoefficientL (1/2 : ℝ) k b)).symm
  exact hLeft.trans ((congrArg (fun z : ℝ => (k : ℝ) * z) hComm).trans hRight.symm)


/-- Exact degree compatibility `J (D_{3/2} x) = D_{1/2} (I x)`, proved by coefficients. -/
lemma shiftedDegree_high_half_compat (x : SphereSobolev (3/2 : ℝ)) :
    JL (DH x) = DL (IH x) := by
  apply sphereSobolev_ext (-(1/2 : ℝ))
  intro k
  have h1 : sphereSobolevCoefficientL (-(1/2 : ℝ)) k (JL (DH x)) =
      sphereSobolevCoefficientL (1/2 : ℝ) k (DH x) :=
    sphereSobolevCoefficientL_inclusion (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (DH x) k
  have h2 : sphereSobolevCoefficientL (1/2 : ℝ) k (DH x) =
      sphereSobolevCoefficientL ((3/2 : ℝ) - 1) k (DH x) :=
    congrArg (fun s : ℝ => sphereSobolevCoefficientL s k (DH x))
      (by norm_num : (1/2 : ℝ) = (3/2 : ℝ) - 1)
  have h3 := sphereSobolevCoefficientL_shiftedDegree (3/2 : ℝ) k x
  have h4 : sphereSobolevCoefficientL (-(1/2 : ℝ)) k (DL (IH x)) =
      sphereSobolevCoefficientL ((1/2 : ℝ) - 1) k (DL (IH x)) :=
    congrArg (fun s : ℝ => sphereSobolevCoefficientL s k (DL (IH x)))
      (by norm_num : (-(1/2 : ℝ)) = (1/2 : ℝ) - 1)
  have h5 := sphereSobolevCoefficientL_shiftedDegree (1/2 : ℝ) k (IH x)
  have h6 := sphereSobolevCoefficientL_inclusion (3/2 : ℝ) (1/2 : ℝ) (by norm_num) x k
  rw [h1, h2, h3, h4, h5, h6]

/-- (R) one rotation is skew for the half pairing. -/
lemma halfPairing_rotation_skew (a' b' : Fin 3) (a b : SphereSobolev (1/2 : ℝ)) :
    PP a (sphereSobolevRotationL (1/2 : ℝ) a' b' b) =
      -PP b (sphereSobolevRotationL (1/2 : ℝ) a' b' a) := by
  have h := sphereSobolevDualPairing_half_rotation_skew a' b' b a
  unfold sphereSobolevDualPairing at h ⊢
  rw [← h]
  exact real_inner_comm _ _

/-- (R) the actual angular connection (finite real combination of rotations) is skew. -/
lemma halfPairing_lowerAngular_skew (g : MatrixField) (L q : ℝ) (y : R3) (i : Fin 3)
    (a b : SphereSobolev (1/2 : ℝ)) :
    PP a (referenceLowerHorizontalAngularL g L q y i b) =
      -PP b (referenceLowerHorizontalAngularL g L q y i a) := by
  unfold referenceLowerHorizontalAngularL
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    halfPairing_smul_right, halfPairing_sum_right]
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a' _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b' _
  rw [halfPairing_rotation_skew]
  ring

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevShiftedDegreeL
  sphereSobolevRotationL sphereSobolevCoefficientL sphereSobolevDualPairing
  referenceHighHorizontalAngularL referenceLowerHorizontalAngularL
  referenceMetricGramFrame referenceRadiusHorizontalLogDerivative weightedGreenHighToHalf

private lemma half_pairing_add_add_smul
    (a : SphereSobolev (1/2 : ℝ)) (b c d : SphereSobolev (-(1/2 : ℝ))) (r : ℝ) :
    PP a (b + c + r • d) = PP a b + PP a c + r * PP a d := by
  exact (halfPairing_add_right a (b+c) (r • d)).trans
    (congrArg₂ (fun x y : ℝ => x+y) (halfPairing_add_right a b c) (halfPairing_smul_right a r d))

private lemma green_scale_lower (r s a b c : ℝ) :
    r * (a + -b + s*c) = r*a-r*b+r*s*c := by ring
private lemma green_scale_upper (r s a b c : ℝ) :
    r * (a+b+s*c) = r*a+r*b+r*s*c := by ring
private lemma green_scalar_assembly (l h a b c d e : ℝ)
    (hl : l=a-b+c) (hh : h=d+b+c) (ha : a= -d-e) :
    l= -h-e+2*c := by rw [hl,hh,ha]; ring

private lemma integral_sub_add_split (a b c : R3 → ℝ)
    (ha : Integrable a) (hb : Integrable b) (hc : Integrable c) :
    (∫ y, a y-b y+c y) = (∫ y, a y)-(∫ y, b y)+(∫ y, c y) := by
  exact (integral_add (ha.sub hb) hc).trans
    (congrArg (fun z : ℝ => z + ∫ y, c y) (integral_sub ha hb))
private lemma integral_add_add_split (a b c : R3 → ℝ)
    (ha : Integrable a) (hb : Integrable b) (hc : Integrable c) :
    (∫ y, a y+b y+c y) = (∫ y, a y)+(∫ y, b y)+(∫ y, c y) := by
  exact (integral_add (ha.add hb) hc).trans
    (congrArg (fun z : ℝ => z + ∫ y, c y) (integral_add ha hb))
private lemma half_pairing_high_to_half (a : SphereSobolev (1/2 : ℝ))
    (x : SphereSobolev (3/2 : ℝ)) : PP a (JL (IH x)) = ⟪a, KH x⟫_ℝ := by
  simp only [sphereSobolevDualPairing,weightedGreenHighToHalf,ContinuousLinearMap.comp_apply]

/-- The high weighted action pushed into the negative space by `J`: base, angular and degree parts. -/
lemma referenceHighWeightedHorizontalAction_inclusion (g : MatrixField) (L q : ℝ)
    (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i : Fin 3) :
    JL (referenceHighWeightedHorizontalAction g L q R u y i) =
      JL (IH (fderiv ℝ u y (referenceMetricGramFrame g L (q,y) i))) +
        referenceLowerHorizontalAngularL g L q y i (IH (u y)) +
          referenceRadiusHorizontalLogDerivative g L q R y i • DL (IH (u y)) := by
  have hAng : JL (referenceHighHorizontalAngularL g L q y i (u y)) =
      referenceLowerHorizontalAngularL g L q y i (IH (u y)) := by
    have h := congrArg
      (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T (u y))
      (referenceHorizontalAngularL_high_lower_compatibility g L q y i)
    simpa only [ContinuousLinearMap.comp_apply] using h
  simp only [referenceHighWeightedHorizontalAction,referenceHighHorizontalAction,
    map_add,map_smul,hAng,shiftedDegree_high_half_compat]

/-- Generic-coefficient version: any smooth density, log coefficient, frame and pointwise-skew
angular field. Arbitrary full-output smooth `u`, compact smooth `v`. -/
private def weightedGreenCoefficientExactContract
    (rho f : R3 → ℝ) (X : R3 → R3)
    (A : R3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (hrho : ContDiff ℝ ∞ rho) (hf : ContDiff ℝ ∞ f) (hX : ContDiff ℝ ∞ X)
    (hA : ContDiff ℝ ∞ A) (hskew : ∀ y a b, PP a (A y b) = -PP b (A y a))
    (u : R3 → SphereSobolev (3/2 : ℝ)) (v : R3 → SphereSobolev (1/2 : ℝ))
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) : Prop :=
    (∫ y, rho y * PP (IH (u y)) (JL (fderiv ℝ v y (X y)) + A y (v y) + f y • DL (v y))) =
      -(∫ y, rho y * PP (v y)
          (JL (IH (fderiv ℝ u y (X y))) + A y (IH (u y)) + f y • DL (IH (u y)))) -
        (∫ y, weightedFrameDivergence rho X y * PP (IH (u y)) (JL (v y))) +
          2 * ∫ y, rho y * f y * PP (v y) (DL (IH (u y)))

attribute [local irreducible] weightedGreenCoefficientExactContract

private theorem weightedGreenCoefficientExactContract_proof
    (rho f : R3 → ℝ) (X : R3 → R3)
    (A : R3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (hrho : ContDiff ℝ ∞ rho) (hf : ContDiff ℝ ∞ f) (hX : ContDiff ℝ ∞ X)
    (hA : ContDiff ℝ ∞ A) (hskew : ∀ y a b, PP a (A y b) = -PP b (A y a))
    (u : R3 → SphereSobolev (3/2 : ℝ)) (v : R3 → SphereSobolev (1/2 : ℝ))
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    weightedGreenCoefficientExactContract rho f X A hrho hf hX hA hskew u v hu hv hvc := by
  have hKu : ContDiff ℝ ∞ (fun z => KH (u z)) := (KH).contDiff.comp hu
  have hKd (y : R3) : fderiv ℝ (fun z => KH (u z)) y = (KH).comp (fderiv ℝ u y) :=
    ((KH).hasFDerivAt.comp y ((hu.differentiable (by simp)) y).hasFDerivAt).fderiv
  have hIu : Continuous (fun y => IH (u y)) := (IH).continuous.comp hu.continuous
  -- integrability of the four genuinely different pieces
  have iP1 : Integrable (fun y => rho y * ⟪fderiv ℝ v y (X y), KH (u y)⟫_ℝ) := by
    have hD : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by simp)
    have hDX : Continuous (fun y => fderiv ℝ v y (X y)) := hD.clm_apply hX.continuous
    have hcD : HasCompactSupport (fderiv ℝ v) := hvc.fderiv (𝕜 := ℝ)
    exact integrable_of_vanishing_on_compact_support
      (G := fderiv ℝ v) (h := fun y => rho y * ⟪fderiv ℝ v y (X y), KH (u y)⟫_ℝ)
      (hrho.continuous.mul (hDX.inner hKu.continuous)) hcD
      (fun y hy => by simp only [hy,ContinuousLinearMap.zero_apply,inner_zero_left,mul_zero])

  have iQ1 : Integrable
      (fun y => rho y * ⟪v y, fderiv ℝ (fun z => KH (u z)) y (X y)⟫_ℝ) :=
    integrable_of_vanishing_on_compact_support
      (hrho.continuous.mul (hv.continuous.inner
        ((hKu.continuous_fderiv (by simp)).clm_apply hX.continuous)))
      hvc (fun y hy => by simp [hy])
  have iQ2 : Integrable (fun y => rho y * PP (v y) (A y (IH (u y)))) :=
    integrable_of_vanishing_on_compact_support
      (hrho.continuous.mul (continuous_halfPairing hv.continuous
        (hA.continuous.clm_apply hIu)))
      hvc (fun y hy => by simp [hy, halfPairing_zero_left])
  have iQ3 : Integrable (fun y => rho y * f y * PP (v y) (DL (IH (u y)))) :=
    integrable_of_vanishing_on_compact_support
      ((hrho.continuous.mul hf.continuous).mul (continuous_halfPairing hv.continuous
        ((DL).continuous.comp hIu)))
      hvc (fun y hy => by simp [hy, halfPairing_zero_left])
  -- pointwise splitting of the lower (left) integrand
  have hptL (y : R3) :
      rho y * PP (IH (u y)) (JL (fderiv ℝ v y (X y)) + A y (v y) + f y • DL (v y)) =
        rho y * ⟪fderiv ℝ v y (X y), KH (u y)⟫_ℝ - rho y * PP (v y) (A y (IH (u y))) +
          rho y * f y * PP (v y) (DL (IH (u y))) := by
    have hk : PP (fderiv ℝ v y (X y)) (JL (IH (u y))) =
        ⟪fderiv ℝ v y (X y), KH (u y)⟫_ℝ := by
      simp only [sphereSobolevDualPairing,weightedGreenHighToHalf,ContinuousLinearMap.comp_apply]
    have hExpand := half_pairing_add_add_smul (IH (u y))
      (JL (fderiv ℝ v y (X y))) (A y (v y)) (DL (v y)) (f y)
    have hBase := (halfPairing_inclusion_symm (IH (u y)) (fderiv ℝ v y (X y))).trans hk
    have hAtoms := congrArg₂ (fun x z : ℝ => x + f y * z)
      (congrArg₂ (fun x z : ℝ => x+z) hBase (hskew y (IH (u y)) (v y)))
      (halfPairing_degree_symm (IH (u y)) (v y))
    exact (congrArg (fun z : ℝ => rho y * z) (hExpand.trans hAtoms)).trans
      (green_scale_lower (rho y) (f y) ⟪fderiv ℝ v y (X y), KH (u y)⟫_ℝ
        (PP (v y) (A y (IH (u y)))) (PP (v y) (DL (IH (u y)))))
  -- pointwise splitting of the high (right) integrand
  have hptH (y : R3) :
      rho y * PP (v y) (JL (IH (fderiv ℝ u y (X y))) + A y (IH (u y)) + f y • DL (IH (u y))) =
        rho y * ⟪v y, fderiv ℝ (fun z => KH (u z)) y (X y)⟫_ℝ +
          rho y * PP (v y) (A y (IH (u y))) + rho y * f y * PP (v y) (DL (IH (u y))) := by
    have hk : ⟪v y, fderiv ℝ (fun z => KH (u z)) y (X y)⟫_ℝ =
        PP (v y) (JL (IH (fderiv ℝ u y (X y)))) := by
      rw [hKd y]
      simp only [sphereSobolevDualPairing,weightedGreenHighToHalf,ContinuousLinearMap.comp_apply]
    have hExpand := half_pairing_add_add_smul (v y)
      (JL (IH (fderiv ℝ u y (X y)))) (A y (IH (u y))) (DL (IH (u y))) (f y)
    have hAtoms := congrArg (fun z : ℝ => z + PP (v y) (A y (IH (u y))) +
      f y * PP (v y) (DL (IH (u y)))) hk.symm
    exact (congrArg (fun z : ℝ => rho y * z) (hExpand.trans hAtoms)).trans
      (green_scale_upper (rho y) (f y)
        ⟪v y, fderiv ℝ (fun z => KH (u z)) y (X y)⟫_ℝ
        (PP (v y) (A y (IH (u y)))) (PP (v y) (DL (IH (u y)))))
  have hLeft :
      (∫ y, rho y * PP (IH (u y)) (JL (fderiv ℝ v y (X y)) + A y (v y) + f y • DL (v y))) =
        (∫ y, rho y * ⟪fderiv ℝ v y (X y), KH (u y)⟫_ℝ) -
          (∫ y, rho y * PP (v y) (A y (IH (u y)))) +
            ∫ y, rho y * f y * PP (v y) (DL (IH (u y))) := by
    calc _ = ∫ y, (rho y * ⟪fderiv ℝ v y (X y), KH (u y)⟫_ℝ -
            rho y * PP (v y) (A y (IH (u y))) + rho y * f y * PP (v y) (DL (IH (u y)))) := by
          exact integral_congr_ae (Filter.Eventually.of_forall hptL)
      _ = _ := integral_sub_add_split
        (fun y => rho y * ⟪fderiv ℝ v y (X y), KH (u y)⟫_ℝ)
        (fun y => rho y * PP (v y) (A y (IH (u y))))
        (fun y => rho y * f y * PP (v y) (DL (IH (u y)))) iP1 iQ2 iQ3
  have hHigh :
      (∫ y, rho y * PP (v y)
          (JL (IH (fderiv ℝ u y (X y))) + A y (IH (u y)) + f y • DL (IH (u y)))) =
        (∫ y, rho y * ⟪v y, fderiv ℝ (fun z => KH (u z)) y (X y)⟫_ℝ) +
          (∫ y, rho y * PP (v y) (A y (IH (u y)))) +
            ∫ y, rho y * f y * PP (v y) (DL (IH (u y))) := by
    calc _ = ∫ y, (rho y * ⟪v y, fderiv ℝ (fun z => KH (u z)) y (X y)⟫_ℝ +
            rho y * PP (v y) (A y (IH (u y))) + rho y * f y * PP (v y) (DL (IH (u y)))) := by
          exact integral_congr_ae (Filter.Eventually.of_forall hptH)
      _ = _ := integral_add_add_split
        (fun y => rho y * ⟪v y, fderiv ℝ (fun z => KH (u z)) y (X y)⟫_ℝ)
        (fun y => rho y * PP (v y) (A y (IH (u y))))
        (fun y => rho y * f y * PP (v y) (DL (IH (u y)))) iQ1 iQ2 iQ3
  -- base Green with E = H^{1/2}, g := v (compact), f := J ∘ I ∘ u
  have hG0 : (∫ y, rho y * ⟪fderiv ℝ v y (X y), KH (u y)⟫_ℝ) =
      -(∫ y, rho y * ⟪v y, fderiv ℝ (fun z => KH (u z)) y (X y)⟫_ℝ) -
        ∫ y, weightedFrameDivergence rho X y * ⟪v y, KH (u y)⟫_ℝ :=
    compact_weighted_frame_green rho X (fun z => KH (u z)) v hrho hX hKu hv hvc
  have hDiv : (fun y => weightedFrameDivergence rho X y * ⟪v y, KH (u y)⟫_ℝ) =
      fun y => weightedFrameDivergence rho X y * PP (IH (u y)) (JL (v y)) := by
    funext y
    exact congrArg (fun z : ℝ => weightedFrameDivergence rho X y * z)
      ((half_pairing_high_to_half (v y) (u y)).symm.trans
        (halfPairing_inclusion_symm (IH (u y)) (v y)).symm)
  have hG1 := hG0.trans (congrArg
    (fun f : R3 → ℝ => -(∫ y, rho y * ⟪v y, fderiv ℝ (fun z => KH (u z)) y (X y)⟫_ℝ) - ∫ y, f y)
    hDiv)
  unfold weightedGreenCoefficientExactContract
  exact green_scalar_assembly
    (∫ y, rho y * PP (IH (u y)) (JL (fderiv ℝ v y (X y)) + A y (v y) + f y • DL (v y)))
    (∫ y, rho y * PP (v y) (JL (IH (fderiv ℝ u y (X y))) + A y (IH (u y)) + f y • DL (IH (u y))))
    (∫ y, rho y * ⟪fderiv ℝ v y (X y), KH (u y)⟫_ℝ)
    (∫ y, rho y * PP (v y) (A y (IH (u y))))
    (∫ y, rho y * f y * PP (v y) (DL (IH (u y))))
    (∫ y, rho y * ⟪v y, fderiv ℝ (fun z => KH (u z)) y (X y)⟫_ℝ)
    (∫ y, weightedFrameDivergence rho X y * PP (IH (u y)) (JL (v y)))
    hLeft hHigh hG1


theorem weighted_horizontal_green_of_coefficients
    (rho f : R3 → ℝ) (X : R3 → R3)
    (A : R3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (hrho : ContDiff ℝ ∞ rho) (hf : ContDiff ℝ ∞ f) (hX : ContDiff ℝ ∞ X)
    (hA : ContDiff ℝ ∞ A) (hskew : ∀ y a b, PP a (A y b) = -PP b (A y a))
    (u : R3 → SphereSobolev (3/2 : ℝ)) (v : R3 → SphereSobolev (1/2 : ℝ))
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    (∫ y, rho y * PP (IH (u y)) (JL (fderiv ℝ v y (X y)) + A y (v y) + f y • DL (v y))) =
      -(∫ y, rho y * PP (v y)
          (JL (IH (fderiv ℝ u y (X y))) + A y (IH (u y)) + f y • DL (IH (u y)))) -
        (∫ y, weightedFrameDivergence rho X y * PP (IH (u y)) (JL (v y))) +
          2 * ∫ y, rho y * f y * PP (v y) (DL (IH (u y))) := by
  simpa only [weightedGreenCoefficientExactContract] using
    (weightedGreenCoefficientExactContract_proof rho f X A hrho hf hX hA hskew u v hu hv hvc)

/-- The actual weighted frame divergence `Σ_j D_{e_j}(rho X_i,j)`. -/
def referenceWeightedFrameDivergence (g : MatrixField) (L q : ℝ) (i : Fin 3) (y : R3) : ℝ :=
  weightedFrameDivergence (fun z => referenceDensityFamily g L (q,z))
    (fun z => referenceMetricGramFrame g L (q,z) i) y

/-- **Actual R3 weighted horizontal Green.** Original metric, density, Gram frame, angular
connection and physical degree `k`; arbitrary smooth full-output `u`, compact smooth `v`. -/
private def actualWeightedGreenExactContract
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ) (R : R3 → ℝ)
    (hR : ContDiff ℝ ∞ R) (hr : ∀ y, R y ≠ 0)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (v : R3 → SphereSobolev (1/2 : ℝ))
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (i : Fin 3) : Prop :=
    (∫ y, referenceDensityFamily g L (q,y) *
        PP (IH (u y)) (referenceLowerWeightedHorizontalAction g L q R v y i)) =
      -(∫ y, referenceDensityFamily g L (q,y) *
          PP (v y) (JL (referenceHighWeightedHorizontalAction g L q R u y i))) -
        (∫ y, referenceWeightedFrameDivergence g L q i y * PP (IH (u y)) (JL (v y))) +
          2 * ∫ y, referenceDensityFamily g L (q,y) *
            referenceRadiusHorizontalLogDerivative g L q R y i *
              PP (v y) (JL (DH (u y)))

attribute [local irreducible] actualWeightedGreenExactContract

private theorem actualWeightedGreenExactContract_proof
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ) (R : R3 → ℝ)
    (hR : ContDiff ℝ ∞ R) (hr : ∀ y, R y ≠ 0)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (v : R3 → SphereSobolev (1/2 : ℝ))
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (i : Fin 3) :
    actualWeightedGreenExactContract g hg L q R hR hr u v hu hv hvc i := by
  have hrho : ContDiff ℝ ∞ (fun y => referenceDensityFamily g L (q,y)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hf : ContDiff ℝ ∞ (fun y => referenceRadiusHorizontalLogDerivative g L q R y i) :=
    contDiff_iff_contDiffAt.2 fun y =>
      (contDiffAt_referenceRadiusHorizontalLogDerivative g L hg R (q,y) i
        hR.contDiffAt (hr y)).comp y (contDiffAt_const.prodMk contDiffAt_id)
  have key := weighted_horizontal_green_of_coefficients
    (fun y => referenceDensityFamily g L (q,y))
    (fun y => referenceRadiusHorizontalLogDerivative g L q R y i)
    (fun y => referenceMetricGramFrame g L (q,y) i)
    (fun y => referenceLowerHorizontalAngularL g L q y i)
    hrho hf (contDiff_referenceMetricGramFrame_slice g hg L q i)
    (contDiff_referenceLowerHorizontalAngularL g hg L q i)
    (fun y a b => halfPairing_lowerAngular_skew g L q y i a b) u v hu hv hvc
  have e1 : (∫ y, referenceDensityFamily g L (q,y) *
        PP (IH (u y)) (referenceLowerWeightedHorizontalAction g L q R v y i)) =
      ∫ y, referenceDensityFamily g L (q,y) * PP (IH (u y))
        (JL (fderiv ℝ v y (referenceMetricGramFrame g L (q,y) i)) +
          referenceLowerHorizontalAngularL g L q y i (v y) +
            referenceRadiusHorizontalLogDerivative g L q R y i • DL (v y)) := rfl
  have e2 : (∫ y, referenceDensityFamily g L (q,y) *
        PP (v y) (JL (referenceHighWeightedHorizontalAction g L q R u y i))) =
      ∫ y, referenceDensityFamily g L (q,y) * PP (v y)
        (JL (IH (fderiv ℝ u y (referenceMetricGramFrame g L (q,y) i))) +
          referenceLowerHorizontalAngularL g L q y i (IH (u y)) +
            referenceRadiusHorizontalLogDerivative g L q R y i • DL (IH (u y))) := by
    exact integral_congr_ae (Filter.Eventually.of_forall (fun y => by
      exact congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
        referenceDensityFamily g L (q,y) * PP (v y) z)
        (referenceHighWeightedHorizontalAction_inclusion g L q R u y i)))
  have e3 : (∫ y, referenceDensityFamily g L (q,y) *
        referenceRadiusHorizontalLogDerivative g L q R y i * PP (v y) (JL (DH (u y)))) =
      ∫ y, referenceDensityFamily g L (q,y) *
        referenceRadiusHorizontalLogDerivative g L q R y i * PP (v y) (DL (IH (u y))) := by
    exact integral_congr_ae (Filter.Eventually.of_forall (fun y => by
      exact congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
        referenceDensityFamily g L (q,y) * referenceRadiusHorizontalLogDerivative g L q R y i * PP (v y) z)
        (shiftedDegree_high_half_compat (u y))))
  unfold actualWeightedGreenExactContract referenceWeightedFrameDivergence
  exact e1.trans (key.trans (congrArg₂
    (fun h b : ℝ => -h - (∫ y, weightedFrameDivergence
      (fun z => referenceDensityFamily g L (q,z))
      (fun z => referenceMetricGramFrame g L (q,z) i) y * PP (IH (u y)) (JL (v y))) + 2 * b)
    e2.symm e3.symm))


theorem actual_weighted_horizontal_green
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ) (R : R3 → ℝ)
    (hR : ContDiff ℝ ∞ R) (hr : ∀ y, R y ≠ 0)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (v : R3 → SphereSobolev (1/2 : ℝ))
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (i : Fin 3) :
    (∫ y, referenceDensityFamily g L (q,y) *
        PP (IH (u y)) (referenceLowerWeightedHorizontalAction g L q R v y i)) =
      -(∫ y, referenceDensityFamily g L (q,y) *
          PP (v y) (JL (referenceHighWeightedHorizontalAction g L q R u y i))) -
        (∫ y, referenceWeightedFrameDivergence g L q i y * PP (IH (u y)) (JL (v y))) +
          2 * ∫ y, referenceDensityFamily g L (q,y) *
            referenceRadiusHorizontalLogDerivative g L q R y i *
              PP (v y) (JL (DH (u y))) := by
  simpa only [actualWeightedGreenExactContract] using
    (actualWeightedGreenExactContract_proof g hg L q R hR hr u v hu hv hvc i)


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.WeightedFrameGreen.compact_weighted_coordinate_green
#print axioms OAI.AnisotropicCalderon.WeightedFrameGreen.compact_weighted_frame_green
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.halfPairing_inclusion_symm
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.halfPairing_degree_symm
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.halfPairing_lowerAngular_skew
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.weighted_horizontal_green_of_coefficients
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.actual_weighted_horizontal_green
