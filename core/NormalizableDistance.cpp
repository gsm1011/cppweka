#include "DistanceFunction.hpp"
#include "OptionHandler.hpp"
#include "RevisionHandler.hpp"

using namespace std; 

double NormalizableDistance::distance(Instance first, Instance second, 
				      double cutOffValue, 
				      PerformanceStats stats) {
  double distance = 0;
  int firstI, secondI;
  int firstNumValues = first.numValues();
  int secondNumValues = second.numValues();
  int numAttributes = m_Data.numAttributes();
  int classIndex = m_Data.classIndex();
    
  validate();
    
  for (int p1 = 0, p2 = 0; p1 < firstNumValues || p2 < secondNumValues; ) {
    if (p1 >= firstNumValues)
      firstI = numAttributes;
    else
      firstI = first.index(p1); 

    if (p2 >= secondNumValues)
      secondI = numAttributes;
    else
      secondI = second.index(p2);

    if (firstI == classIndex) {
      p1++; 
      continue;
    }
    if ((firstI < numAttributes) && !m_ActiveIndices[firstI]) {
      p1++; 
      continue;
    }
       
    if (secondI == classIndex) {
      p2++; 
      continue;
    }
    if ((secondI < numAttributes) && !m_ActiveIndices[secondI]) {
      p2++;
      continue;
    }
       
    double diff;
      
    if (firstI == secondI) {
      diff = difference(firstI,
			first.valueSparse(p1),
			second.valueSparse(p2));
      p1++;
      p2++;
    }
    else if (firstI > secondI) {
      diff = difference(secondI, 
			0, second.valueSparse(p2));
      p2++;
    }
    else {
      diff = difference(firstI, 
			first.valueSparse(p1), 0);
      p1++;
    }
    if (stats != NULL)
      stats.incrCoordCount();
      
    distance = updateDistance(distance, diff);
    if (distance > cutOffValue)
      return Double.POSITIVE_INFINITY;
  }

  return distance;
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
double NormalizableDistance::difference(int index, double val1, double val2) {
  switch (m_Data.attribute(index).type()) {
  case Attribute.NOMINAL:
    if (Instance.isMissingValue(val1) ||
	Instance.isMissingValue(val2) ||
	((int) val1 != (int) val2)) {
      return 1;
    }
    else {
      return 0;
    }
        
  case Attribute.NUMERIC:
    if (Instance.isMissingValue(val1) ||
	Instance.isMissingValue(val2)) {
      if (Instance.isMissingValue(val1) &&
	  Instance.isMissingValue(val2)) {
	if (!m_DontNormalize)  //We are doing normalization
	  return 1;
	else
	  return (m_Ranges[index][R_MAX] - m_Ranges[index][R_MIN]);
      }
      else {
	double diff;
	if (Instance.isMissingValue(val2)) {
	  diff = (!m_DontNormalize) ? norm(val1, index) : val1;
	}
	else {
	  diff = (!m_DontNormalize) ? norm(val2, index) : val2;
	}
	if (!m_DontNormalize && diff < 0.5) {
	  diff = 1.0 - diff;
	}
	else if (m_DontNormalize) {
	  if ((m_Ranges[index][R_MAX]-diff) > (diff-m_Ranges[index][R_MIN]))
	    return m_Ranges[index][R_MAX]-diff;
	  else
	    return diff-m_Ranges[index][R_MIN];
	}
	return diff;
      }
    }
    else {
      return (!m_DontNormalize) ? 
	(norm(val1, index) - norm(val2, index)) :
	(val1 - val2);
    }
        
  default:
    return 0;
  }
}

double[][] NormalizableDistance::initializeRanges() {
  if (m_Data == NULL) {
    m_Ranges = NULL;
    return m_Ranges;
  }
    
  int numAtt = m_Data.numAttributes();
  double[][] ranges = new double [numAtt][3];
    
  if (m_Data.numInstances() <= 0) {
    initializeRangesEmpty(numAtt, ranges);
    m_Ranges = ranges;
    return m_Ranges;
  }
  else {
    // initialize ranges using the first instance
    updateRangesFirst(m_Data.instance(0), numAtt, ranges);
  }
    
  // update ranges, starting from the second
  for (int i = 1; i < m_Data.numInstances(); i++)
    updateRanges(m_Data.instance(i), numAtt, ranges);

  m_Ranges = ranges;
    
  return m_Ranges;
}
  
void NormalizableDistance::updateRangesFirst(Instance instance, 
					     int numAtt, double[][] ranges) {
  for (int j = 0; j < numAtt; j++) {
    if (!instance.isMissing(j)) {
      ranges[j][R_MIN] = instance.value(j);
      ranges[j][R_MAX] = instance.value(j);
      ranges[j][R_WIDTH] = 0.0;
    }
    else { // if value was missing
      ranges[j][R_MIN] = Double.POSITIVE_INFINITY;
      ranges[j][R_MAX] = -Double.POSITIVE_INFINITY;
      ranges[j][R_WIDTH] = Double.POSITIVE_INFINITY;
    }
  }
}
  
void NormalizableDistance::updateRanges(Instance instance, int numAtt, 
					double[][] ranges) {
  // updateRangesFirst must have been called on ranges
  for (int j = 0; j < numAtt; j++) {
    double value = instance.value(j);
    if (!instance.isMissing(j)) {
      if (value < ranges[j][R_MIN]) {
	ranges[j][R_MIN] = value;
	ranges[j][R_WIDTH] = ranges[j][R_MAX] - ranges[j][R_MIN];
	if (value > ranges[j][R_MAX]) { //if this is the first value that is
	  ranges[j][R_MAX] = value;    //not missing. The,0
	  ranges[j][R_WIDTH] = ranges[j][R_MAX] - ranges[j][R_MIN];
	}
      }
      else {
	if (value > ranges[j][R_MAX]) {
	  ranges[j][R_MAX] = value;
	  ranges[j][R_WIDTH] = ranges[j][R_MAX] - ranges[j][R_MIN];
	}
      }
    }
  }
}
  
/**
 * Updates the ranges given a new instance.
 * 
 * @param instance 	the new instance
 * @param ranges 	low, high and width values for all attributes
 * @return		the updated ranges
 */
double[][] NormalizableDistance::updateRanges(Instance instance, 
					      double[][] ranges) {
  // updateRangesFirst must have been called on ranges
  for (int j = 0; j < ranges.length; j++) {
    double value = instance.value(j);
    if (!instance.isMissing(j)) {
      if (value < ranges[j][R_MIN]) {
	ranges[j][R_MIN] = value;
	ranges[j][R_WIDTH] = ranges[j][R_MAX] - ranges[j][R_MIN];
      } else {
	if (instance.value(j) > ranges[j][R_MAX]) {
	  ranges[j][R_MAX] = value;
	  ranges[j][R_WIDTH] = ranges[j][R_MAX] - ranges[j][R_MIN];
	}
      }
    }
  }
    
  return ranges;
}
  
/**
 * Initializes the ranges of a subset of the instances of this dataset.
 * Therefore m_Ranges is not set.
 * 
 * @param instList 	list of indexes of the subset
 * @return 		the ranges
 * @throws Exception	if something goes wrong
 */
double[][] NormalizableDistance::initializeRanges(int[] instList) throw(Exception) {
  if (m_Data == NULL)
    throw Exception("No instances supplied.");
    
  int numAtt = m_Data.numAttributes();
  double[][] ranges = new double [numAtt][3];
    
  if (m_Data.numInstances() <= 0) {
    initializeRangesEmpty(numAtt, ranges);
    return ranges;
  }
  else {
    // initialize ranges using the first instance
    updateRangesFirst(m_Data.instance(instList[0]), numAtt, ranges);
    // update ranges, starting from the second
    for (int i = 1; i < instList.length; i++) {
      updateRanges(m_Data.instance(instList[i]), numAtt, ranges);
    }
  }
  return ranges;
}

double[][] NormalizableDistance::initializeRanges(int[] instList, 
						  int startIdx, 
						  int endIdx) throw( Exception) {
  if (m_Data == NULL)
    throw Exception("No instances supplied.");
    
  int numAtt = m_Data.numAttributes();
  double[][] ranges = new double [numAtt][3];
    
  if (m_Data.numInstances() <= 0) {
    initializeRangesEmpty(numAtt, ranges);
    return ranges;
  }
  else {
    // initialize ranges using the first instance
    updateRangesFirst(m_Data.instance(instList[startIdx]), numAtt, ranges);
    // update ranges, starting from the second
    for (int i = startIdx+1; i <= endIdx; i++) {
      updateRanges(m_Data.instance(instList[i]), numAtt, ranges);
    }
  }
    
  return ranges;
}

bool NormalizableDistance::inRanges(Instance instance, double[][] ranges) {
  bool isIn = true;
    
  // updateRangesFirst must have been called on ranges
  for (int j = 0; isIn && (j < ranges.length); j++) {
    if (!instance.isMissing(j)) {
      double value = instance.value(j);
      isIn = value <= ranges[j][R_MAX];
      if (isIn) isIn = value >= ranges[j][R_MIN];
    }
  }
    
  return isIn;
}
