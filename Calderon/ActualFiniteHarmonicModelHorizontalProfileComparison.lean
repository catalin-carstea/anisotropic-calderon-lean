import Calderon.ActualFiniteHarmonicModelCoframeGradientBounds

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame SectionFiveErrorForms
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev horizontalProfileFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] horizontalProfileFunction

def finiteCoreReferenceProfileEnergy (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam beta : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  sourceNormSquareIntegrand beta
    (fun a : Fin 3 => coreReferenceHorizontal hO hD g hg L lam a F x)
    (coreWeightOperator hO hD (besselWeight 1) F x)
    (fun a : Fin 3 => coreWeightOperator hO hD (besselWeight (1/2:ℝ))
      (coreReferenceHorizontal hO hD g hg L lam a F) x)
    (coreWeightOperator hO hD (besselWeight (3/2:ℝ)) F x)

lemma finiteCoreReferenceProfileEnergy_nonneg (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam beta : ℝ) (hb : 0 ≤ beta) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    0 ≤ finiteCoreReferenceProfileEnergy hO hD g hg L lam beta F x :=
  sourceNormSquareIntegrand_nonneg beta hb _ _ _ _

lemma coordinate_profile_energy_le
    (beta C a b c d A B : ℝ) (hb : 1 ≤ beta) (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hb0 : 0 ≤ b) (hd : 0 ≤ d)
    (ha : a ≤ C*(A+b)) (hc : c ≤ C*(B+d)) :
    a+beta^2*b+beta⁻¹*c+beta*d ≤ (C+1)*(A+beta^2*b+beta⁻¹*B+beta*d) := by
  have hpos : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  have hi : 0 ≤ beta⁻¹ := inv_nonneg.mpr hpos.le
  have hs : 1 ≤ beta^2 := by nlinarith [sq_nonneg (beta-1)]
  have hib : beta⁻¹ ≤ beta := by
    nlinarith [mul_nonneg hi (sub_nonneg.mpr hb),inv_mul_cancel₀ hpos.ne']
  have hbb : 0 ≤ C*(beta^2-1)*b := mul_nonneg (mul_nonneg hC (sub_nonneg.mpr hs)) hb0
  have hdd : 0 ≤ C*(beta-beta⁻¹)*d := mul_nonneg (mul_nonneg hC (sub_nonneg.mpr hib)) hd
  have hBi := mul_nonneg hi hB
  calc
    _ ≤ C*(A+b)+beta^2*b+beta⁻¹*(C*(B+d))+beta*d :=
      add_le_add (add_le_add (add_le_add ha le_rfl) (mul_le_mul_of_nonneg_left hc hi)) le_rfl
    _ = (C+1)*(A+beta^2*b+beta⁻¹*B+beta*d)-
        (A+beta⁻¹*B+C*(beta^2-1)*b+C*(beta-beta⁻¹)*d) := by ring
    _ ≤ _ := by linarith

theorem exists_finiteCoreSourceEnergy_uniform_reference_profile_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      ∀ beta : ℝ, 1 ≤ beta → ∀ F : smoothCompactFiniteSphereCore hO hD,
      finiteCoreSourceEnergy hO hD beta F x ≤
        C*finiteCoreReferenceProfileEnergy hO hD g hg L lam beta F x := by
  obtain ⟨C,hC,hgrad⟩ := exists_coordinate_gradient_uniform_horizontal_bounds hO hD g hg L K hK
  refine ⟨C+1,by linarith,?_⟩
  intro lam hlam x hx beta hb F
  have hh := hgrad lam hlam x hx F
  unfold finiteCoreSourceEnergy finiteCoreReferenceProfileEnergy sourceNormSquareIntegrand
  apply coordinate_profile_energy_le beta C _ _ _ _ _ _ hb hC.le
    (Finset.sum_nonneg (fun a _ => sq_nonneg _)) (Finset.sum_nonneg (fun a _ => sq_nonneg _))
    (sq_nonneg _) (sq_nonneg _) hh.1 hh.2

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
