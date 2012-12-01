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
#include <iostream>
#include <string>
#include <vector>
#include "NormalizableDistance.hpp"
using namespace std; 

/**
 * Represents the abstract ancestor for string-based distance functions, like
 * EditDistance.
 *
 * @author Bruno Woltzenlogel Paleo
 * @version $Revision: 1.1 $
 */
class AbstractStringDistanceFunction : public NormalizableDistance {
  
  /**
   * Constructor that doesn't set the data
   */
public:
  AbstractStringDistanceFunction() {
    ///super();
  }

  /**
   * Constructor that sets the data
   *
   * @param data the set of instances that will be used for
   * later distance comparisons
   */
  AbstractStringDistanceFunction(Instances data) {
    //super(data);
  }

    
  /**
   * Updates the current distance calculated so far with the new difference
   * between two attributes. The difference between the attributes was 
   * calculated with the difference(int,double,double) method.
   * 
   * @param currDist	the current distance calculated so far
   * @param diff	the difference between two new attributes
   * @return		the update distance
   * @see		#difference(int, double, double)
   */
protected:
  double updateDistance(double currDist, double diff) {
    return (currDist + (diff * diff));
  }

  /**
   * Computes the difference between two given attribute
   * values.
   * 
   * @param index	the attribute index
   * @param val1	the first value
   * @param val2	the second value
   * @return		the difference
   */

  double difference(int index, string string1, string string2); 
  
  /**
   * Calculates the distance between two instances. Offers speed up (if the 
   * distance function class in use supports it) in nearest neighbour search by 
   * taking into account the cutOff or maximum distance. Depending on the 
   * distance function class, post processing of the distances by 
   * postProcessDistances(double []) may be required if this function is used.
   *
   * @param first 	the first instance
   * @param second 	the second instance
   * @param cutOffValue If the distance being calculated becomes larger than 
   *                    cutOffValue then the rest of the calculation is 
   *                    discarded.
   * @param stats 	the performance stats object
   * @return 		the distance between the two given instances or 
   * 			Double.POSITIVE_INFINITY if the distance being 
   * 			calculated becomes larger than cutOffValue. 
   */
  //@Override
public:
  double distance(Instance first, Instance second, 
		  double cutOffValue, PerformanceStats stats);
  /**
   * Calculates the distance between two strings.
   * Must be implemented by any non-abstract StringDistance class
   *
   * @param stringA the first string
   * @param stringB the second string
   * @return the distance between the two given strings
   */
  virtual double stringDistance(string stringA, string stringB);

};
