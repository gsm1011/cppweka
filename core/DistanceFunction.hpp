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
 *    DistanceFunction.cpp
 *    Copyright (C) 1999-2005 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core;

// import weka.core.neighboursearch.PerformanceStats;
#include <string>
#include "OptionHandler.hpp"
#include "Instances.hpp"
#include "Instance.hpp"
#include "neighboursearch/PerformanceStats.hpp"

using namespace std; 
/**
 * Interface for any class that can compute and return distances between two
 * instances.
 *
 * @author  Ashraf M. Kibriya (amk14@cs.waikato.ac.nz)
 * @version $Revision: 1.7 $ 
 */
class DistanceFunction : public OptionHandler {
public:
  /**
   * Sets the instances.
   * 
   * @param insts 	the instances to use
   */
  virtual void setInstances(Instances insts) = 0;

  /**
   * returns the instances currently set.
   * 
   * @return 		the current instances
   */
  virtual Instances getInstances() = 0;

  /**
   * Sets the range of attributes to use in the calculation of the distance.
   * The indices start from 1, 'first' and 'last' are valid as well. 
   * E.g.: first-3,5,6-last
   * 
   * @param value	the new attribute index range
   */
  virtual void setAttributeIndices(string value) = 0;
  
  /**
   * Gets the range of attributes used in the calculation of the distance.
   * 
   * @return		the attribute index range
   */
  virtual string getAttributeIndices() = 0;
  
  /**
   * Sets whether the matching sense of attribute indices is inverted or not.
   * 
   * @param value	if true the matching sense is inverted
   */
  virtual void setInvertSelection(bool value) = 0;
  
  /**
   * Gets whether the matching sense of attribute indices is inverted or not.
   * 
   * @return		true if the matching sense is inverted
   */
  virtual bool getInvertSelection() = 0;

  /**
   * Calculates the distance between two instances.
   * 
   * @param first 	the first instance
   * @param second 	the second instance
   * @return 		the distance between the two given instances
   */
  virtual double distance(Instance first, Instance second) = 0;

  /**
   * Calculates the distance between two instances.
   * 
   * @param first 	the first instance
   * @param second 	the second instance
   * @param stats 	the performance stats object
   * @return 		the distance between the two given instances
   * @throws Exception 	if calculation fails
   */
  virtual double distance(Instance first, Instance second, 
			  PerformanceStats stats) throw(Exception) = 0;

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
   * @return 		the distance between the two given instances or 
   * 			Double.POSITIVE_INFINITY if the distance being 
   * 			calculated becomes larger than cutOffValue. 
   */
  virtual double distance(Instance first, Instance second, double cutOffValue) = 0;

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
  virtual double distance(Instance first, Instance second, 
      double cutOffValue, PerformanceStats stats) = 0;

  /**
   * Does post processing of the distances (if necessary) returned by
   * distance(distance(Instance first, Instance second, double cutOffValue). It
   * may be necessary, depending on the distance function, to do post processing
   * to set the distances on the correct scale. Some distance function classes
   * may not return correct distances using the cutOffValue distance function to 
   * minimize the inaccuracies resulting from floating point comparison and 
   * manipulation.
   * 
   * @param distances	the distances to post-process
   */
  virtual void postProcessDistances(double distances[]) = 0;

  /**
   * Update the distance function (if necessary) for the newly added instance.
   * 
   * @param ins		the instance to add
   */
  virtual void update(Instance ins) = 0;
};
