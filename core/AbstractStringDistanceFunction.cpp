/*
 *    This program is free software; you can redistribute it and/or modify
 *    it under the terms of the GNU General Public License as published by
 *    the Free Software Foundation; either version 2 of the License, or
 *    (at your option) any later version.
 *
 *    This program is distributed in the hope that it will be useful,
 *    but WITHOUT ANY WARRANTY; without even the implied warranty of
 *    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *    GNU General Public License for more details.
 *
 *    You should have received a copy of the GNU General Public License
 *    along with this program; if not, write to the Free Software
 *    Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 */

/*
 *    AbstractStringDistanceFunction.cpp
 */
#include "AbstractStringDistanceFunction.hpp"
using namespace std;

double AbstractStringDistanceFunction::difference(int index,
        string string1,
        string string2) {
    switch (m_Data.attribute(index).type()) {
    case Attribute.STRING:
        double diff = stringDistance(string1, string2);
        if (m_DontNormalize == true) {
            return diff;
        } else {
            if (string1.length() > string2.length()) {
                return diff/((double) string1.length());
            } else {
                return diff/((double) string2.length());
            }
        }

    default:
        return 0;
    }
}

double AbstractStringDistanceFunction::distance(Instance first, Instance second,
        double cutOffValue,
        PerformanceStats stats) {
    double sqDistance = 0;
    int numAttributes = m_Data.numAttributes();

    validate();

    double diff;

    for (int i = 0; i < numAttributes; i++) {
        diff = 0;
        if (m_ActiveIndices[i]) {
            diff = difference(i, first.stringValue(i), second.stringValue(i));
        }
        sqDistance = updateDistance(sqDistance, diff);
        if (sqDistance > (cutOffValue * cutOffValue)) return Double.POSITIVE_INFINITY;
    }
    double distance = sqrt(sqDistance);
    return distance;
}
