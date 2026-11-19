



























































































void AP_AHRS::calc_trig(const Matrix3f &rot,
                        float &cr, float &cp, float &cy,
                        float &sr, float &sp, float &sy) const
{
    Vector2f yaw_vector(rot.a.x, rot.b.x);

    if (fabsf(yaw_vector.x) > 0 ||
        fabsf(yaw_vector.y) > 0) {
        yaw_vector.normalize();
    }
    sy = constrain_float(yaw_vector.y, -1.0f, 1.0f);
    cy = constrain_float(yaw_vector.x, -1.0f, 1.0f);

    // sanity checks
    if (yaw_vector.is_inf() || yaw_vector.is_nan()) {
        sy = 0.0f;
        cy = 1.0f;
    }

    const float cx2 = rot.c.x * rot.c.x;
    if (cx2 >= 1.0f) {
        cp = 0;
        cr = 1.0f;
    } else {
        cp = safe_sqrt(1 - cx2);
        cr = rot.c.z / cp;
    }
    cp = constrain_float(cp, 0.0f, 1.0f);
    cr = constrain_float(cr, -1.0f, 1.0f); // this relies on constrain_float() of infinity doing the right thing

    sp = -rot.c.x;

    if (!is_zero(cp)) {
        sr = rot.c.y / cp;
    }

    if (is_zero(cp) || isinf(cr) || isnan(cr) || isinf(sr) || isnan(sr)) {
        float r, p, y;
        rot.to_euler(&r, &p, &y);
        cr = cosf(r);
        sr = sinf(r);
    }
}
