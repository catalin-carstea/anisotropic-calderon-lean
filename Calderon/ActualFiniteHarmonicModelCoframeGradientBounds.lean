import Calderon.ActualFiniteHarmonicModelCoframeReconstruction
import Calderon.ActualFiniteHarmonicModelCoframeSquareBound
import Calderon.ActualFiniteHarmonicModelReferenceConnectionNorms

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  ActualReferenceDDHigherGeometryJets CoordinateBootstrapJets PrincipalCommutator ActualHorizontalNormBridge ReferenceDensityBounds
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev coframeGradientFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] coframeGradientFunction

lemma sum_norm_coframe_sum_sub_sq_le
    (c : Fin 3 → Fin 3 → ℝ) (X Y : Fin 3 → SphereL2) (J s : ℝ)
    (hJ : 0 ≤ J) (hs : 0 ≤ s) (hc : ∀ j a, |c j a| ≤ J) (hY : ∀ a, ‖Y a‖ ≤ J*s) :
    (∑ j : Fin 3, ‖∑ a : Fin 3, c j a • (X a-Y a)‖^2) ≤
      (18*J^2+54*J^4)*((∑ a : Fin 3, ‖X a‖^2)+s^2) := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    norm_coframe_sum_sub_sq_le (c j) X Y J s hJ hs (hc j) hY)
  have hQ : 0 ≤ ∑ a : Fin 3, ‖X a‖^2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  calc
    _ ≤ ∑ _j : Fin 3, (6*J^2*(∑ a : Fin 3, ‖X a‖^2)+18*J^4*s^2) := hsum
    _ = 18*J^2*(∑ a : Fin 3, ‖X a‖^2)+54*J^4*s^2 := by simp only [Fin.sum_univ_three]; ring
    _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg J) (sq_nonneg s),
      mul_nonneg (show 0 ≤ J^4 by positivity) hQ]

theorem exists_coordinate_gradient_uniform_horizontal_bounds
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      ∀ F : smoothCompactFiniteSphereCore hO hD,
      (∑ j : Fin 3, ‖coreDirectionalDerivative hO hD (coordinateDirection j) F x‖^2) ≤
        C*((∑ a : Fin 3, ‖coreReferenceHorizontal hO hD g hg L lam a F x‖^2)+
          ‖coreWeightOperator hO hD (besselWeight 1) F x‖^2) ∧
      (∑ j : Fin 3, ‖coreWeightOperator hO hD (besselWeight (1/2:ℝ))
        (coreDirectionalDerivative hO hD (coordinateDirection j) F) x‖^2) ≤
        C*((∑ a : Fin 3, ‖coreWeightOperator hO hD (besselWeight (1/2:ℝ))
          (coreReferenceHorizontal hO hD g hg L lam a F) x‖^2)+
          ‖coreWeightOperator hO hD (besselWeight (3/2:ℝ)) F x‖^2) := by
  obtain ⟨M,hM,hgeom⟩ := exists_referenceDD_fixed_geometry_uniform_coordinate_word_bounds hO hD g hg L K hK 0
  obtain ⟨CA,hCA,hconn⟩ := exists_nativeReferenceConnection_uniform_norm_bounds hO hD g hg L K hK
  let J := M+CA+1
  have hJ : 0 ≤ J := by dsimp only [J]; linarith
  have hMle : M ≤ J := by dsimp only [J]; linarith
  have hCAle : CA ≤ J := by dsimp only [J]; linarith
  have hJpos : 0 < J := by dsimp only [J]; linarith
  refine ⟨18*J^2+54*J^4,by positivity,?_⟩
  intro lam hlam x hx F
  let c := fun j a : Fin 3 => referenceCoFrameEntry g L j a (lam,x)
  have hc (j a : Fin 3) : |c j a| ≤ J := by
    exact (show |c j a| ≤ M by
      simpa only [c,coordinateFieldWordPartial] using (hgeom lam hlam x hx [] (by simp)).2.2.1 j a).trans hMle
  have h0 (j : Fin 3) : coreDirectionalDerivative hO hD (coordinateDirection j) F x =
      ∑ a : Fin 3, c j a • (coreReferenceHorizontal hO hD g hg L lam a F x-
        nativeReferenceConnectionAction hO hD g hg L lam a F x) := by
    have he := congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
      (coreCoordinateDerivative_eq_coframe_horizontal_sub_connection hO hD g hg L lam j)
    simpa only [c,LinearMap.sum_apply,Submodule.coe_sum,Finset.sum_apply,Module.End.mul_apply,
      nativeReferenceCoFrameScalar,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,
      LinearMap.sub_apply,Submodule.coe_sub,Pi.sub_apply] using he
  constructor
  · simp_rw [h0]
    apply sum_norm_coframe_sum_sub_sq_le c _ _ J _ hJ (norm_nonneg _) hc
    intro a
    exact (hconn lam hlam x hx a F).1.trans (mul_le_mul_of_nonneg_right hCAle (norm_nonneg _))
  · simp_rw [coreWeight_half_coordinateDerivative_eq_coframe_horizontal_sub_connection hO hD g hg L lam]
    apply sum_norm_coframe_sum_sub_sq_le c _ _ J _ hJ (norm_nonneg _) hc
    intro a
    exact (hconn lam hlam x hx a F).2.trans (mul_le_mul_of_nonneg_right hCAle (norm_nonneg _))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
