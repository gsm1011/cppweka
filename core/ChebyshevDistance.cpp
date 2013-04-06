#include "ChebyshevDistance.hpp"

TechnicalInformation ChebyshevDistance::getTechnicalInformation() {
    TechnicalInformation 	result;
    
    result = new TechnicalInformation(Type.MISC);
    result.setValue(Field.AUTHOR, "Wikipedia");
    result.setValue(Field.TITLE, "Chebyshev distance");
    result.setValue(Field.URL, "http://en.wikipedia.org/wiki/Chebyshev_distance");

    return result;
}
