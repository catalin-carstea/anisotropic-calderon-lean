import Calderon.ShrinkingGeometry

/- Finite robustness component of the shrinking-sphere argument.
   Actual metric comparison and curvature estimates remain separate obligations. -/

namespace OAI.AnisotropicCalderon.ShrinkingPerturbation

open ShrinkingGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma sq_bounds_of_abs_sub_le (x y η : ℝ) (_hη : 0 ≤ η) (h : |x-y| ≤ η) :
    y ^ 2 - 2 * |y| * η ≤ x ^ 2 ∧ x ^ 2 ≤ y ^ 2 + 2 * |y| * η + η ^ 2 := by
  have hp : |y * (x-y)| ≤ |y| * η := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg y)
  have hp₁ := (abs_le.mp hp).1
  have hp₂ := (abs_le.mp hp).2
  have he : (x-y)^2 ≤ η^2 := by
    have he₁ := (abs_le.mp h).1
    have he₂ := (abs_le.mp h).2
    nlinarith
  constructor <;> nlinarith [sq_nonneg (x-y)]

lemma norm_perpendicularComponent_le (ω z : E) (hω : ‖ω‖=1) :
    ‖perpendicularComponent ω z‖ ≤ ‖z‖ := by
  have h := norm_perpendicularComponent_sq ω z hω
  nlinarith [sq_nonneg (inner ℝ ω z), norm_nonneg z,
    norm_nonneg (perpendicularComponent ω z)]

lemma abs_norm_perpendicularComponent_sub_le (ω x y : E) (hω : ‖ω‖=1) :
    |‖perpendicularComponent ω x‖ - ‖perpendicularComponent ω y‖| ≤ ‖x-y‖ := by
  have h := abs_norm_sub_norm_le (perpendicularComponent ω x) (perpendicularComponent ω y)
  rw [← perpendicularComponent_sub] at h
  exact h.trans (norm_perpendicularComponent_le ω (x-y) hω)

lemma minimized_residual_identity (ω u w : E) (hω : ‖ω‖=1)
    (huw : inner ℝ u w=0) (hu : ‖u‖^2 ≠ 0) (hw : ‖w‖^2=1/‖u‖^2) :
    ‖perpendicularComponent ω (ω-(1/‖u‖^2) • u)‖^2 +
      (1-‖perpendicularComponent ω w‖)^2 -
      (inner ℝ (u-ω) ((1/‖u‖^2) • u))^2 - (inner ℝ (u-ω) w)^2 =
    2 * (‖perpendicularComponent ω w‖^2-‖perpendicularComponent ω w‖ +
      inner ℝ ω u/‖u‖^2-(inner ℝ ω u/‖u‖^2)^2) := by
  have hreal : perpendicularComponent ω (ω-(1/‖u‖^2) • u) =
      -(1/‖u‖^2) • perpendicularComponent ω u := by
    rw [perpendicularComponent_sub, perpendicularComponent_self ω hω,
      perpendicularComponent_smul]
    module
  rw [hreal, norm_smul_sq, norm_perpendicularComponent_sq ω u hω]
  simp only [inner_sub_left, inner_smul_right, huw, zero_sub,
    real_inner_self_eq_norm_sq]
  have hp := norm_perpendicularComponent_sq ω w hω
  rw [hw] at hp
  have hn0 : ‖u‖ ≠ 0 := fun h => hu (by simp [h])
  field_simp [hn0] at hp ⊢
  nlinarith only [congrArg (fun s : ℝ => ‖u‖ ^ 2 * s) hp]

lemma model_sizes (ω b w₀ : E) (hω : ‖ω‖ = 1) (hb : ‖b‖ ≤ 1 / 4)
    (huw : inner ℝ (ω+b) w₀ = 0) (hw : ‖w₀‖ = 1 / ‖ω+b‖) :
    ‖(1 / ‖ω+b‖ ^ 2) • (ω+b)‖ ≤ 2 ∧ ‖w₀‖ ≤ 2 ∧
    ‖perpendicularComponent ω (ω-(1 / ‖ω+b‖ ^ 2) • (ω+b))‖ ≤ 2 * ‖b‖ ∧
    |1-‖perpendicularComponent ω w₀‖| ≤ 3 * ‖b‖ := by
  have hslo : 3 / 4 ≤ ‖ω+b‖ := by
    have ht := norm_add_le (ω+b) (-b)
    simp only [add_neg_cancel_right,norm_neg,hω] at ht
    linarith
  have hspos : 0 < ‖ω+b‖ := by linarith
  have hsne : ‖ω+b‖ ≠ 0 := ne_of_gt hspos
  have hinv : 1 / ‖ω+b‖ ≤ 3 / 2 := by
    apply (div_le_iff₀ hspos).2
    linarith
  have hqnorm : ‖(1 / ‖ω+b‖ ^ 2) • (ω+b)‖ = 1 / ‖ω+b‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    field_simp [hsne]
  have hww : ‖w₀‖ ≤ 3 / 2 := by rw [hw]; exact hinv
  have hD : 0 < ‖ω+b‖ ^ 2 := by positivity
  have hinvD : 1 / ‖ω+b‖ ^ 2 ≤ 2 := by
    apply (div_le_iff₀ hD).2
    nlinarith
  have hreal : perpendicularComponent ω (ω-(1 / ‖ω+b‖ ^ 2) • (ω+b)) =
      -(1 / ‖ω+b‖ ^ 2) • perpendicularComponent ω b := by
    simp only [perpendicularComponent,inner_sub_right,inner_smul_right,inner_add_right,
      real_inner_self_eq_norm_sq,hω,one_pow]
    module
  have hrealbound : ‖perpendicularComponent ω (ω-(1 / ‖ω+b‖ ^ 2) • (ω+b))‖ ≤ 2*‖b‖ := by
    rw [hreal,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (by positivity)]
    calc
      (1 / ‖ω+b‖ ^ 2) * ‖perpendicularComponent ω b‖ ≤
          (1 / ‖ω+b‖ ^ 2) * ‖b‖ :=
        mul_le_mul_of_nonneg_left (norm_perpendicularComponent_le ω b hω) (by positivity)
      _ ≤ 2*‖b‖ := mul_le_mul_of_nonneg_right hinvD (norm_nonneg b)
  have hz : |inner ℝ ω w₀| ≤ (3 / 2)*‖b‖ := by
    have hu' : inner ℝ ω w₀ = -inner ℝ b w₀ := by
      rw [inner_add_left] at huw
      linarith
    rw [hu',abs_neg]
    exact (abs_real_inner_le_norm b w₀).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hww (norm_nonneg b)])
  have hprojdiff : ‖perpendicularComponent ω w₀-w₀‖ = |inner ℝ ω w₀| := by
    have hid : perpendicularComponent ω w₀-w₀ = -(inner ℝ ω w₀) • ω := by
      simp only [perpendicularComponent]
      module
    rw [hid,norm_smul,Real.norm_eq_abs,abs_neg,hω,mul_one]
  have hprojclose : |‖perpendicularComponent ω w₀‖-‖w₀‖| ≤ (3 / 2)*‖b‖ := by
    exact (abs_norm_sub_norm_le _ _).trans (hprojdiff.le.trans hz)
  have hsclose : |‖ω+b‖-1| ≤ ‖b‖ := by
    simpa only [hω,add_sub_cancel_left] using abs_norm_sub_norm_le (ω+b) ω
  have hinvclose : |1-‖w₀‖| ≤ (3 / 2)*‖b‖ := by
    rw [hw]
    have hid : 1-1 / ‖ω+b‖ = (‖ω+b‖-1) / ‖ω+b‖ := by field_simp [hsne]
    rw [hid,abs_div,abs_of_nonneg (norm_nonneg _)]
    calc
      |‖ω+b‖-1| / ‖ω+b‖ = |‖ω+b‖-1| * (1 / ‖ω+b‖) := by ring
      _ ≤ ‖b‖ * (1 / ‖ω+b‖) := mul_le_mul_of_nonneg_right hsclose (by positivity)
      _ ≤ ‖b‖ * (3 / 2) := mul_le_mul_of_nonneg_left hinv (norm_nonneg b)
      _ = (3 / 2)*‖b‖ := by ring
  have himag : |1-‖perpendicularComponent ω w₀‖| ≤ 3*‖b‖ := by
    calc
      |1-‖perpendicularComponent ω w₀‖| =
          |(1-‖w₀‖)+(‖w₀‖-‖perpendicularComponent ω w₀‖)| := by congr 1; ring
      _ ≤ |1-‖w₀‖|+|‖w₀‖-‖perpendicularComponent ω w₀‖| := abs_add_le _ _
      _ ≤ 3*‖b‖ := by rw [abs_sub_comm ‖w₀‖]; linarith
  constructor
  · rw [hqnorm]; linarith
  constructor
  · linarith
  exact ⟨hrealbound,himag⟩

lemma model_minimized_residual_nonneg (ω b w₀ : E) (hω : ‖ω‖=1)
    (hb : ‖b‖≤1/4) (huw : inner ℝ (ω+b) w₀=0)
    (hw : ‖w₀‖=1/‖ω+b‖) :
    0 ≤ ‖perpendicularComponent ω (ω-(1/‖ω+b‖^2) • (ω+b))‖^2 +
      (1-‖perpendicularComponent ω w₀‖)^2 -
      (inner ℝ b ((1/‖ω+b‖^2) • (ω+b)))^2 - (inner ℝ b w₀)^2 := by
  have ha : |inner ℝ ω b| ≤ 1/4 := by
    have hcs := abs_real_inner_le_norm ω b
    simpa [hω] using hcs.trans (by simpa [hω] using hb)
  have hnorm : ‖ω+b‖^2=1+2*inner ℝ ω b+‖b‖^2 := by
    simpa [hω] using norm_add_sq_real ω b
  have hm : inner ℝ ω (ω+b)=1+inner ℝ ω b := by simp [inner_add_right,hω]
  have ha₁ := (abs_le.mp ha).1
  have hu : 0<‖ω+b‖^2 := by nlinarith [sq_nonneg ‖b‖]
  have hm₀ : 0 ≤ inner ℝ ω (ω+b) := by linarith
  have hsmall : ‖ω+b‖^2≤2*inner ℝ ω (ω+b) := by nlinarith [norm_nonneg b]
  have hw' : ‖w₀‖^2=1/‖ω+b‖^2 := by rw [hw,div_pow,one_pow]
  have hid := minimized_residual_identity ω (ω+b) w₀ hω huw (ne_of_gt hu) hw'
  simp only [add_sub_cancel_left] at hid
  rw [hid]
  have hxk := norm_perpendicularComponent_ge_normalized_inner ω (ω+b) w₀ hω hu hm₀ huw hw'
  have hx : 1 / 2 ≤ inner ℝ ω (ω+b)/‖ω+b‖^2 := by
    apply (le_div_iff₀ hu).2
    linarith
  have hf := residual_factor_nonneg ‖perpendicularComponent ω w₀‖
    (inner ℝ ω (ω+b)/‖ω+b‖^2) hx hxk
  linarith

lemma abs_inner_sub_le (b x y : E) (η : ℝ) (h : ‖x-y‖ ≤ η) :
    |inner ℝ b x-inner ℝ b y| ≤ ‖b‖*η := by
  rw [← inner_sub_right]
  exact (abs_real_inner_le_norm b (x-y)).trans
    (mul_le_mul_of_nonneg_left h (norm_nonneg b))

lemma imaginary_projection_sq_lower (ω v w : E) (hωv : inner ℝ ω v=0)
    (hv : ‖v‖=1) :
    (1-‖perpendicularComponent ω w‖)^2 ≤ ‖perpendicularComponent ω (v-w)‖^2 := by
  rw [perpendicularComponent_sub,perpendicularComponent_eq_self ω v hωv,
    norm_sub_sq_real,hv,one_pow]
  have hinner := real_inner_le_norm v (perpendicularComponent ω w)
  rw [hv,one_mul] at hinner
  nlinarith only [hinner]

theorem shrinking_sphere_residual_perturbation (ω b v w₀ q w : E) (η : ℝ)
    (hω : ‖ω‖=1) (hv : ‖v‖=1) (hωv : inner ℝ ω v=0)
    (hb : ‖b‖≤1/4) (hη : 0≤η)
    (huw : inner ℝ (ω+b) w₀=0) (hw₀ : ‖w₀‖=1/‖ω+b‖)
    (hqclose : ‖q-(1/‖ω+b‖^2) • (ω+b)‖≤η) (hwclose : ‖w-w₀‖≤η) :
    -(16*(‖b‖*η+η^2)) ≤
      ‖perpendicularComponent ω (ω-q)‖^2+‖perpendicularComponent ω (v-w)‖^2-
      (inner ℝ b q)^2-(inner ℝ b w)^2 := by
  let q₀ : E := (1/‖ω+b‖^2) • (ω+b)
  have hmodel := model_minimized_residual_nonneg ω b w₀ hω hb huw hw₀
  have hs := model_sizes ω b w₀ hω hb huw hw₀
  obtain ⟨hqsize,hwsize,hrealsize,himagsize⟩ := hs
  have hrealclose : |‖perpendicularComponent ω (ω-q)‖-
      ‖perpendicularComponent ω (ω-q₀)‖|≤η := by
    have h := abs_norm_perpendicularComponent_sub_le ω (ω-q) (ω-q₀) hω
    have hid : (ω-q)-(ω-q₀) = -(q-q₀) := by module
    rw [hid,norm_neg] at h
    exact h.trans hqclose
  have hreal := (sq_bounds_of_abs_sub_le ‖perpendicularComponent ω (ω-q)‖
    ‖perpendicularComponent ω (ω-q₀)‖ η hη hrealclose).1
  rw [abs_of_nonneg (norm_nonneg _)] at hreal
  have hrealerror : ‖perpendicularComponent ω (ω-q₀)‖^2-4*‖b‖*η ≤
      ‖perpendicularComponent ω (ω-q)‖^2 := by
    have h := mul_le_mul_of_nonneg_right hrealsize hη
    nlinarith only [h,hreal]
  have hkclose : |‖perpendicularComponent ω w‖-‖perpendicularComponent ω w₀‖|≤η :=
    (abs_norm_perpendicularComponent_sub_le ω w w₀ hω).trans hwclose
  have hikclose : |(1-‖perpendicularComponent ω w‖)-
      (1-‖perpendicularComponent ω w₀‖)|≤η := by
    have hid : (1-‖perpendicularComponent ω w‖)-(1-‖perpendicularComponent ω w₀‖) =
        -(‖perpendicularComponent ω w‖-‖perpendicularComponent ω w₀‖) := by ring
    rw [hid,abs_neg]
    exact hkclose
  have himag := (sq_bounds_of_abs_sub_le (1-‖perpendicularComponent ω w‖)
    (1-‖perpendicularComponent ω w₀‖) η hη hikclose).1
  have himagerror : (1-‖perpendicularComponent ω w₀‖)^2-6*‖b‖*η ≤
      ‖perpendicularComponent ω (v-w)‖^2 := by
    have h := mul_le_mul_of_nonneg_right himagsize hη
    have hi := imaginary_projection_sq_lower ω v w hωv hv
    nlinarith only [h,himag,hi]
  have hpair : ∀ z z₀ : E, ‖z-z₀‖≤η → ‖z₀‖≤2 →
      (inner ℝ b z)^2 ≤ (inner ℝ b z₀)^2+4*‖b‖^2*η+‖b‖^2*η^2 := by
    intro z z₀ hclose hsize
    have hclose' := abs_inner_sub_le b z z₀ η hclose
    have hη' : 0≤‖b‖*η := mul_nonneg (norm_nonneg b) hη
    have hsq := (sq_bounds_of_abs_sub_le (inner ℝ b z) (inner ℝ b z₀)
      (‖b‖*η) hη' hclose').2
    have hsize' : |inner ℝ b z₀|≤2*‖b‖ := by
      have hc := abs_real_inner_le_norm b z₀
      have hh := mul_le_mul_of_nonneg_left hsize (norm_nonneg b)
      nlinarith only [hc,hh]
    have hh := mul_le_mul_of_nonneg_right hsize' hη'
    nlinarith only [hsq,hh]
  have hqpair := hpair q q₀ hqclose hqsize
  have hwpair := hpair w w₀ hwclose hwsize
  have hB₀ : 0≤‖b‖ := norm_nonneg b
  have he₁ : 8*‖b‖^2*η≤2*‖b‖*η := by
    have he : 8*‖b‖^2≤2*‖b‖ := by nlinarith only [hb,hB₀]
    exact mul_le_mul_of_nonneg_right he hη
  have he₂ : 2*‖b‖^2*η^2≤(1/8)*η^2 := by
    have he : 2*‖b‖^2≤1/8 := by nlinarith only [hb,hB₀]
    exact mul_le_mul_of_nonneg_right he (sq_nonneg η)
  change 0 ≤ ‖perpendicularComponent ω (ω-q₀)‖^2+
    (1-‖perpendicularComponent ω w₀‖)^2-(inner ℝ b q₀)^2-(inner ℝ b w₀)^2 at hmodel
  nlinarith only [hmodel,hrealerror,himagerror,hqpair,hwpair,he₁,he₂,
    mul_nonneg hB₀ hη,sq_nonneg η]

theorem exists_radially_normalized_tangent (u w : E) (η : ℝ)
    (hu₀ : 0 < ‖u‖) (hu₁ : ‖u‖ ≤ 5 / 4) (hη : η ≤ 1 / 4)
    (huw : inner ℝ u w=0) (hclose : |‖w‖-1 / ‖u‖| ≤ η) :
    ∃ w₀ : E, inner ℝ u w₀=0 ∧ ‖w₀‖=1 / ‖u‖ ∧ ‖w-w₀‖≤η := by
  have hule : 4 / 5 ≤ 1 / ‖u‖ := by
    apply (le_div_iff₀ hu₀).2
    linarith
  have hw₀ : 0 < ‖w‖ := by
    have h := (abs_le.mp hclose).1
    linarith
  have hunz : ‖u‖ ≠ 0 := ne_of_gt hu₀
  have hwnz : ‖w‖ ≠ 0 := ne_of_gt hw₀
  let a : ℝ := 1 / (‖u‖*‖w‖)
  let w₀ : E := a • w
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hnormal : ‖w₀‖=1 / ‖u‖ := by
    dsimp [w₀]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha]
    dsimp [a]
    field_simp [hunz,hwnz]
  have hdiff : w-w₀=(1-a) • w := by dsimp [w₀]; module
  have hdist : ‖w-w₀‖=|‖w‖-1 / ‖u‖| := by
    rw [hdiff,norm_smul,Real.norm_eq_abs]
    have hm : |1-a| * ‖w‖=|(1-a)*‖w‖| := by
      rw [abs_mul,abs_of_nonneg (norm_nonneg w)]
    rw [hm]
    congr 1
    dsimp [a]
    field_simp [hunz,hwnz]
  refine ⟨w₀,?_,hnormal,?_⟩
  · simp [w₀,inner_smul_right,huw]
  · rw [hdist]; exact hclose

theorem exists_shrinking_sphere_model_tangent (ω b w : E) (η : ℝ)
    (hω : ‖ω‖=1) (hb : ‖b‖≤1 / 4) (hη : η≤1 / 4)
    (huw : inner ℝ (ω+b) w=0) (hclose : |‖w‖-1 / ‖ω+b‖|≤η) :
    ∃ w₀ : E, inner ℝ (ω+b) w₀=0 ∧ ‖w₀‖=1 / ‖ω+b‖ ∧ ‖w-w₀‖≤η := by
  have hlo : 3 / 4≤‖ω+b‖ := by
    have h := norm_add_le (ω+b) (-b)
    simp only [add_neg_cancel_right,norm_neg,hω] at h
    linarith
  have hup : ‖ω+b‖≤5 / 4 := by
    have h := norm_add_le ω b
    rw [hω] at h
    linarith
  exact exists_radially_normalized_tangent (ω+b) w η (by linarith) hup hη huw hclose

theorem shrinking_sphere_perturbed_hessian_lower_bound
    (ω b v w₀ q w : E) (η r c β : ℝ) (H : E → E → ℝ)
    (hω : ‖ω‖=1) (hv : ‖v‖=1) (hωv : inner ℝ ω v=0)
    (hb : ‖b‖≤1/4) (hη₀ : 0≤η) (hη₁ : η≤1/4)
    (huw : inner ℝ (ω+b) w₀=0) (hw₀ : ‖w₀‖=1/‖ω+b‖)
    (hqclose : ‖q-(1/‖ω+b‖^2) • (ω+b)‖≤η) (hwclose : ‖w-w₀‖≤η)
    (hc : 0≤c) (hβ : 0≤β) (hH : ∀ x, H x x≤-(c*β)*‖x‖^2) :
    (1/2)*c*r^2*β-16*(‖b‖*η+η^2) ≤
      ‖perpendicularComponent ω (ω-q)‖^2+‖perpendicularComponent ω (v-w)‖^2-
      (inner ℝ b q)^2-(inner ℝ b w)^2-r^2*(H q q+H w w) := by
  have hR := shrinking_sphere_residual_perturbation ω b v w₀ q w η
    hω hv hωv hb hη₀ huw hw₀ hqclose hwclose
  let q₀ : E := (1/‖ω+b‖^2) • (ω+b)
  have hslo : 3/4≤‖ω+b‖ := by
    have h := norm_add_le (ω+b) (-b)
    simp only [add_neg_cancel_right,norm_neg,hω] at h
    linarith
  have hspos : 0<‖ω+b‖ := by linarith
  have hsne : ‖ω+b‖≠0 := ne_of_gt hspos
  have hsupper : ‖ω+b‖≤5/4 := by
    have h := norm_add_le ω b
    rw [hω] at h
    linarith
  have hinvlo : 4/5≤1/‖ω+b‖ := by
    apply (le_div_iff₀ hspos).2
    linarith
  have hqnorm : ‖q₀‖=1/‖ω+b‖ := by
    dsimp [q₀]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    field_simp [hsne]
  have hqlow : 1/2≤‖q‖ := by
    have h := (abs_norm_sub_norm_le q q₀).trans hqclose
    rw [hqnorm] at h
    have h' := (abs_le.mp h).1
    linarith
  have hwlow : 1/2≤‖w‖ := by
    have h := (abs_norm_sub_norm_le w w₀).trans hwclose
    rw [hw₀] at h
    have h' := (abs_le.mp h).1
    linarith
  have hnorms : 1/2≤‖q‖^2+‖w‖^2 := by nlinarith only [hqlow,hwlow]
  have hHsum := add_le_add (hH q) (hH w)
  have hmul := mul_le_mul_of_nonneg_left hnorms (mul_nonneg hc hβ)
  have hsum : H q q+H w w≤-(1/2)*(c*β) := by nlinarith only [hHsum,hmul]
  have hrH := mul_le_mul_of_nonneg_left hsum (sq_nonneg r)
  nlinarith only [hR,hrH]

#print axioms shrinking_sphere_residual_perturbation
#print axioms exists_shrinking_sphere_model_tangent
#print axioms shrinking_sphere_perturbed_hessian_lower_bound

end OAI.AnisotropicCalderon.ShrinkingPerturbation
