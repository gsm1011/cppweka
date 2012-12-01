#include "PerformanceStats.hpp"

using namespace std; 

double PerformanceStats::getMeasure(string additionalMeasureName) throw(IllegalArgumentException) {
  if (additionalMeasureName.compareToIgnoreCase("measureTotal_points_visited") == 0) {
    return (double) getTotalPointsVisited();
  } else if (additionalMeasureName.compareToIgnoreCase("measureMean_points_visited") == 0) {
    return (double) getMeanPointsVisited();
  } else if (additionalMeasureName.compareToIgnoreCase("measureStdDev_points_visited") == 0) {
    return (double) getStdDevPointsVisited();
  } else if (additionalMeasureName.compareToIgnoreCase("measureMin_points_visited") == 0) {
    return (double) getMinPointsVisited();
  } else if (additionalMeasureName.compareToIgnoreCase("measureMax_points_visited") == 0) {
    return (double) getMaxPointsVisited();
  }
  //coord stats
  else if (additionalMeasureName.compareToIgnoreCase("measureTotalCoordsPerPoint") == 0) {
    return (double) getTotalCoordsPerPoint();
  } else if (additionalMeasureName.compareToIgnoreCase("measureMeanCoordsPerPoint") == 0) {
    return (double) getMeanCoordsPerPoint();
  } else if (additionalMeasureName.compareToIgnoreCase("measureStdDevCoordsPerPoint") == 0) {
    return (double) getStdDevCoordsPerPoint();
  } else if (additionalMeasureName.compareToIgnoreCase("measureMinCoordsPerPoint") == 0) {
    return (double) getMinCoordsPerPoint();
  } else if (additionalMeasureName.compareToIgnoreCase("measureMaxCoordsPerPoint") == 0) {
    return (double) getMaxCoordsPerPoint();
  } else {
    throw(new IllegalArgumentException(additionalMeasureName 
				       + " not supported by PerformanceStats."));
  }
}
