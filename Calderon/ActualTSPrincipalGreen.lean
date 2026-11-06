import Calderon.ActualHigherSScalarCommutatorForm

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalGreen
open PrincipalCommutator ActualHigherSScalarCommutatorForm ActualHigherSScalarCommutatorCoefficients

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def firstForm (P : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (u : R3 → E)
    (A : R3 → E →L[ℝ] F) (X Y : R3) : ℝ :=
  ∫ x, mu x*P (directionalFDeriv X u x) (A x (directionalFDeriv Y u x))

def secondForm (P : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (u : R3 → E)
    (A : R3 → E →L[ℝ] F) (X Y : R3) : ℝ :=
  ∫ x, mu x*P (u x) (A x (directionalFDeriv X (directionalFDeriv Y u) x))

/-- Both actual differentiated coefficients are retained, with the original density. -/
def lowerForm (P : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (u : R3 → E)
    (A : R3 → E →L[ℝ] F) (X Y : R3) : ℝ :=
  ∫ x, directionalFDeriv X mu x*P (u x) (A x (directionalFDeriv Y u x))+
    mu x*P (u x) ((directionalFDeriv X A x) (directionalFDeriv Y u x))

/-- Integrability of the literal first row needs coefficient smoothness only on support. -/
lemma firstForm_integrable
    (P : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (u : R3 → E)
    (A : R3 → E →L[ℝ] F) (K : Set R3) (hK : IsCompact K)
    (hm : Continuous mu) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K, u x = 0) (hA : ∀ x ∈ K, ContDiffAt ℝ ∞ A x) (X Y : R3) :
    Integrable (fun x => mu x*P (directionalFDeriv X u x) (A x (directionalFDeriv Y u x))) := by
  exact integrable_weighted_supported_operator_pair P mu (directionalFDeriv X u)
    (directionalFDeriv Y u) A K hK hm (contDiff_directionalFDeriv X u hu).continuous
    (contDiff_directionalFDeriv Y u hu)
    (fun x hx => directional_eq_zero_off u K hK.isClosed h0 Y x hx) hA

/-- Integrability of the full second row is obtained from derivative locality. -/
lemma secondForm_integrable
    (P : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (u : R3 → E)
    (A : R3 → E →L[ℝ] F) (K : Set R3) (hK : IsCompact K)
    (hm : Continuous mu) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K, u x = 0) (hA : ∀ x ∈ K, ContDiffAt ℝ ∞ A x) (X Y : R3) :
    Integrable (fun x => mu x*P (u x) (A x (directionalFDeriv X (directionalFDeriv Y u) x))) := by
  have hv : ContDiff ℝ ∞ (directionalFDeriv Y u) := contDiff_directionalFDeriv Y u hu
  have hv0 : ∀ x ∉ K, directionalFDeriv Y u x=0 :=
    fun x hx => directional_eq_zero_off u K hK.isClosed h0 Y x hx
  exact integrable_weighted_supported_operator_pair P mu u _ A K hK hm hu.continuous
    (contDiff_directionalFDeriv X _ hv)
    (fun x hx => directional_eq_zero_off _ K hK.isClosed hv0 X x hx) hA

/-- Both density and operator derivative terms in the lower row are integrable. -/
lemma lowerForm_integrable
    (P : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (u : R3 → E)
    (A : R3 → E →L[ℝ] F) (K : Set R3) (hK : IsCompact K)
    (hm : ContDiff ℝ ∞ mu) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K, u x = 0) (hA : ∀ x ∈ K, ContDiffAt ℝ ∞ A x) (X Y : R3) :
    Integrable (fun x => directionalFDeriv X mu x*P (u x) (A x (directionalFDeriv Y u x))+
      mu x*P (u x) ((directionalFDeriv X A x) (directionalFDeriv Y u x))) := by
  have hv := contDiff_directionalFDeriv Y u hu
  have hv0 : ∀ x ∉ K, directionalFDeriv Y u x=0 :=
    fun x hx => directional_eq_zero_off u K hK.isClosed h0 Y x hx
  exact (integrable_weighted_supported_operator_pair P (directionalFDeriv X mu) u _ A K hK
    (contDiff_directionalFDeriv X mu hm).continuous hu.continuous hv hv0 hA).add
    (integrable_weighted_supported_operator_pair P mu u _ (directionalFDeriv X A) K hK
      hm.continuous hu.continuous hv hv0 (fun x hx => contDiffAt_directional A x X (hA x hx)))

/-- Literal one-step Green decomposition, with all three integrals justified. -/
theorem secondForm_add_firstForm_add_lowerForm
    (P : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (u : R3 → E)
    (A : R3 → E →L[ℝ] F) (K : Set R3) (hK : IsCompact K)
    (hm : ContDiff ℝ ∞ mu) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K, u x = 0) (hA : ∀ x ∈ K, ContDiffAt ℝ ∞ A x) (X Y : R3) :
    secondForm P mu u A X Y+firstForm P mu u A X Y+lowerForm P mu u A X Y = 0 := by
  let v := directionalFDeriv Y u
  have hv : ContDiff ℝ ∞ v := contDiff_directionalFDeriv Y u hu
  have hv0 : ∀ x ∉ K, v x = 0 := fun x hx => directional_eq_zero_off u K hK.isClosed h0 Y x hx
  have hD : ∀ x ∈ K, ContDiffAt ℝ ∞ (directionalFDeriv X A) x :=
    fun x hx => contDiffAt_directional A x X (hA x hx)
  have hi0 := integrable_weighted_supported_operator_pair P (directionalFDeriv X mu) u v A K hK
    (contDiff_directionalFDeriv X mu hm).continuous hu.continuous hv hv0 hA
  have hi1 := firstForm_integrable P mu u A K hK hm.continuous hu h0 hA X Y
  have hi2 := integrable_weighted_supported_operator_pair P mu u v (directionalFDeriv X A) K hK
    hm.continuous hu.continuous hv hv0 hD
  have hg := weighted_second_operator_green P mu u A K hK hm hu h0 hA X Y
  have hs01 := integral_add hi0 hi1
  have hs012 := integral_add (hi0.add hi1) hi2
  have hs02 := integral_add hi0 hi2
  simp only [Pi.add_apply,v] at hs01 hs012 hs02
  rw [hs012,hs01] at hg
  unfold secondForm firstForm lowerForm
  rw [hs02]
  linarith only [hg]

/-- The paired first row is the coordinate-swapped original first row. -/
lemma firstForm_adjoint_swap
    (P : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (u : R3 → E)
    (A At : R3 → E →L[ℝ] F)
    (K : Set R3) (hK : IsClosed K) (h0 : ∀ x ∉ K, u x = 0)
    (hAt : ∀ x ∈ K, ∀ v w, P v (At x w)=P w (A x v)) (X Y : R3) :
    firstForm P mu u At X Y = firstForm P mu u A Y X := by
  unfold firstForm
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · exact congrArg (fun z : ℝ => mu x*z) (hAt x hx _ _)
  · simp only [directional_eq_zero_off u K hK h0 X x hx,
      directional_eq_zero_off u K hK h0 Y x hx,map_zero,zero_apply,mul_zero]

/-- The antisymmetric part becomes the difference of the two literal lower rows. -/
theorem firstForm_sub_adjoint
    (P : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (u : R3 → E)
    (A At : R3 → E →L[ℝ] F) (K : Set R3) (hK : IsCompact K)
    (hm : ContDiff ℝ ∞ mu) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K, u x = 0) (hA : ∀ x ∈ K, ContDiffAt ℝ ∞ A x)
    (hAt : ∀ x ∈ K, ∀ v w, P v (At x w)=P w (A x v)) (X Y : R3) :
    firstForm P mu u A X Y-firstForm P mu u At X Y =
      lowerForm P mu u A Y X-lowerForm P mu u A X Y := by
  have hxy := secondForm_add_firstForm_add_lowerForm P mu u A K hK hm hu h0 hA X Y
  have hyx := secondForm_add_firstForm_add_lowerForm P mu u A K hK hm hu h0 hA Y X
  have hs : secondForm P mu u A X Y=secondForm P mu u A Y X := by
    unfold secondForm
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => congrArg
      (fun z : E => mu x*P (u x) (A x z)) (directionalFDeriv_commute X Y u hu x))
  rw [firstForm_adjoint_swap P mu u A At K hK.isClosed h0 hAt X Y]
  linarith only [hxy,hyx,hs]

/-- Literal symmetric coefficient equality transfers to the two first forms. -/
lemma firstForm_symmetric_sum
    (P : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (u : R3 → E)
    (A At C Ct : R3 → E →L[ℝ] F) (K : Set R3) (hK : IsCompact K)
    (hm : Continuous mu) (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x = 0)
    (hA : ∀ x ∈ K, ContDiffAt ℝ ∞ A x) (hAt : ∀ x ∈ K, ContDiffAt ℝ ∞ At x)
    (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x) (hCt : ∀ x ∈ K, ContDiffAt ℝ ∞ Ct x)
    (hsym : ∀ x ∈ K, A x+At x=C x+Ct x) (X Y : R3) :
    firstForm P mu u A X Y+firstForm P mu u At X Y =
      firstForm P mu u C X Y+firstForm P mu u Ct X Y := by
  have hiA := firstForm_integrable P mu u A K hK hm hu h0 hA X Y
  have hiAt := firstForm_integrable P mu u At K hK hm hu h0 hAt X Y
  have hiC := firstForm_integrable P mu u C K hK hm hu h0 hC X Y
  have hiCt := firstForm_integrable P mu u Ct K hK hm hu h0 hCt X Y
  unfold firstForm
  rw [← integral_add hiA hiAt,← integral_add hiC hiCt]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · have he := congrArg (fun T : E →L[ℝ] F => mu x*P (directionalFDeriv X u x)
      (T (directionalFDeriv Y u x))) (hsym x hx)
    simpa only [ContinuousLinearMap.add_apply,map_add,mul_add] using he
  · simp only [directional_eq_zero_off u K hK.isClosed h0 Y x hx,map_zero,mul_zero,add_zero]


/-- Exact principal cancellation; coefficient and density first rows remain explicit. -/
theorem principal_signed_form_eq_gained_second_and_lower
    (P : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (u : R3 → E)
    (A At C Ct : R3 → E →L[ℝ] F) (K : Set R3) (hK : IsCompact K)
    (hm : ContDiff ℝ ∞ mu) (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x = 0)
    (hA : ∀ x ∈ K, ContDiffAt ℝ ∞ A x) (hAt : ∀ x ∈ K, ContDiffAt ℝ ∞ At x)
    (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x) (hCt : ∀ x ∈ K, ContDiffAt ℝ ∞ Ct x)
    (hAadj : ∀ x ∈ K, ∀ v w, P v (At x w)=P w (A x v))
    (hCadj : ∀ x ∈ K, ∀ v w, P v (Ct x w)=P w (C x v))
    (hsym : ∀ x ∈ K, A x+At x=C x+Ct x) (X Y : R3) :
    firstForm P mu u A X Y = -secondForm P mu u C X Y-
      (lowerForm P mu u C X Y+lowerForm P mu u C Y X)/2+
      (lowerForm P mu u A Y X-lowerForm P mu u A X Y)/2 := by
  have hsymI := firstForm_symmetric_sum P mu u A At C Ct K hK hm.continuous hu h0
    hA hAt hC hCt hsym X Y
  have hAI := firstForm_sub_adjoint P mu u A At K hK hm hu h0 hA hAadj X Y
  have hCI := firstForm_sub_adjoint P mu u C Ct K hK hm hu h0 hC hCadj X Y
  have hCJ := secondForm_add_firstForm_add_lowerForm P mu u C K hK hm hu h0 hC X Y
  linarith only [hsymI,hAI,hCI,hCJ]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalGreen
