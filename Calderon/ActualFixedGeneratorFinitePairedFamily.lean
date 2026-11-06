import Calderon.ActualFixedGeneratorLowConstruction
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFixedGeneratorFinitePairedFamily
open SphereHarmonic ActualFullEGainedEndpoints ActualGeneratorEPairedGainedEndpoints
  ActualAngularHighDraft ActualAngularPiDraft
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "I33" => sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
attribute [local irreducible] sphereSobolevInclusionL

private lemma high_operator_norm_nonneg (T : Hi →L[ℝ] Half) : 0 ≤ ‖T‖ := by
  change 0 ≤ sInf {c : ℝ | 0 ≤ c ∧ ∀ v : Hi, ‖T v‖ ≤ c*‖v‖}
  exact Real.sInf_nonneg (fun _ h => h.1)

private lemma low_operator_norm_nonneg (T : Half →L[ℝ] Neg) : 0 ≤ ‖T‖ := by
  change 0 ≤ sInf {c : ℝ | 0 ≤ c ∧ ∀ v : Half, ‖T v‖ ≤ c*‖v‖}
  exact Real.sInf_nonneg (fun _ h => h.1)

private lemma exists_uniform_finite_pair_bound {ι : Type*} [Fintype ι]
    (f g : ι → ι → ℝ) (hf : ∀ V W, 0 ≤ f V W) (hg : ∀ V W, 0 ≤ g V W) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ V W, f V W ≤ M ∧ g V W ≤ M := by
  classical
  let S : ℝ := ∑ z : ι × ι, (f z.1 z.2+g z.1 z.2)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun z _ => add_nonneg (hf z.1 z.2) (hg z.1 z.2))
  refine ⟨1+S,by linarith,?_⟩
  intro V W
  have hOne : f V W+g V W ≤ S :=
    Finset.single_le_sum (fun z _ => add_nonneg (hf z.1 z.2) (hg z.1 z.2))
      (Finset.mem_univ (V,W))
  constructor <;> linarith [hf V W,hg V W]

theorem exists_finite_paired_family {ι : Type*} [Fintype ι]
    (Ch : ι → ι → Hi →L[ℝ] Half)
    (hAdj : ∀ V W, ∀ U Z : Hi,
      PP (IH Z) (JL (Ch V W U)) = PP (IH U) (JL (Ch W V Z))) :
    ∃ Cl : ι → ι → Half →L[ℝ] Neg,
      (∀ V W,
        (Cl V W).comp IH = (JL).comp (Ch V W) ∧
        (I33).comp (Cl V W) = (v016TransposeL (Ch W V)).comp JL ∧
        ‖Cl V W‖ ≤ (‖Ch V W‖+‖Ch W V‖)/2) ∧
      ∃ M : ℝ, 1 ≤ M ∧ ∀ V W, ‖Ch V W‖ ≤ M ∧ ‖Cl V W‖ ≤ M := by
  classical
  have hExists (V W : ι) : ∃ Cl : Half →L[ℝ] Neg,
      Cl.comp IH = (JL).comp (Ch V W) ∧
      (I33).comp Cl = (v016TransposeL (Ch W V)).comp JL ∧
      ‖Cl‖ ≤ (‖Ch V W‖+‖Ch W V‖)/2 :=
    ActualFixedGeneratorLowConstruction.exists_constant_paired_low (Ch V W) (Ch W V) (hAdj V W)
  let Cl : ι → ι → Half →L[ℝ] Neg := fun V W => Classical.choose (hExists V W)
  have hCl (V W : ι) :
      (Cl V W).comp IH = (JL).comp (Ch V W) ∧
      (I33).comp (Cl V W) = (v016TransposeL (Ch W V)).comp JL ∧
      ‖Cl V W‖ ≤ (‖Ch V W‖+‖Ch W V‖)/2 := Classical.choose_spec (hExists V W)
  have hHigh0 : ∀ V W : ι, 0 ≤ ‖Ch V W‖ := fun V W => high_operator_norm_nonneg (Ch V W)
  have hLow0 : ∀ V W : ι, 0 ≤ ‖Cl V W‖ := fun V W => low_operator_norm_nonneg (Cl V W)
  have hBounds : ∃ M : ℝ, 1 ≤ M ∧ ∀ V W : ι, ‖Ch V W‖ ≤ M ∧ ‖Cl V W‖ ≤ M :=
    exists_uniform_finite_pair_bound (fun V W => ‖Ch V W‖) (fun V W => ‖Cl V W‖) hHigh0 hLow0
  exact ⟨Cl,hCl,hBounds⟩
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFixedGeneratorFinitePairedFamily
