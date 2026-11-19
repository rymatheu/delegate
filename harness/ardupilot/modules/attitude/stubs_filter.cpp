// stubs_filter.cpp: the filter-definition singleton and the notch filter.
//
//   symbol                                   why it is outside the stage, and what stands in
//   AP::filters(), AP_Filters::get_filter    the filter-definition singleton (FILT* parameters).
//                                            Reached only through AC_PID::set_notch_sample_rate
//                                            when a notch index is set; the rate-PID stand-ins
//                                            keep NTF = NEF = 0, so the constructor's call
//                                            returns at once. Abort.
//   NotchFilter<float>::apply, ::reset       the notch filter (its source pulls in MAVLink
//                                            logging); only AC_PID::update_all, which the stage
//                                            never calls. Abort.
#include <Filter/AP_Filter.h>
#include <Filter/NotchFilter.h>

AP_Filters &AP::filters()
{
    unreachable("AP::filters");
}

AP_Filter *AP_Filters::get_filter(uint8_t filt_num)
{
    unreachable("AP_Filters::get_filter");
}

template <>
float NotchFilter<float>::apply(const float &sample)
{
    unreachable("NotchFilter<float>::apply");
}

template <>
void NotchFilter<float>::reset()
{
    unreachable("NotchFilter<float>::reset");
}
