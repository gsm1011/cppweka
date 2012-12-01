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
 * TreePerformanceStats.java
 * Copyright (C) 2007 University of Waikato, Hamilton, New Zealand
 */

// package weka.core.neighboursearch;

// import weka.core.RevisionUtils;

// import java.util.Enumeration;
// import java.util.Vector;

/**
 * The class that measures the performance of a tree based 
 * nearest neighbour search algorithm.
 * 
 * @author Ashraf M. Kibriya (amk14[at-the-rate]cs[dot]waikato[dot]ac[dot]nz)
 * @version $Revision: 1.2 $
 */
class TreePerformanceStats : public PerformanceStats {
  
  /** for serialization. */
private: const static long serialVersionUID = -6637636693340810373L;
  
protected:
  // Variables for leaves
  /** The min and max number leaf nodes looked 
   * for a query by the tree based NNS algorithm. */
  int m_MinLeaves, m_MaxLeaves;
  
  /** The sum of leaf nodes looked 
   * at for all the queries. 
   */
  int m_SumLeaves;
  /** The squared sum of leaf nodes looked 
   * at for all the queries. 
   */
  int m_SumSqLeaves;
  /** The number of leaf nodes looked at
   * for the current/last query.
   */
  int m_LeafCount;
  
  // Variables for internal nodes
  /** The min and max number internal nodes looked 
   * for a query by the tree based NNS algorithm. */
  int m_MinIntNodes, m_MaxIntNodes;
  /** The sum of internal nodes looked 
   * at for all the queries. 
   */
  int m_SumIntNodes;
  /** The squared sum of internal nodes looked 
   * at for all the queries. 
   */
  int m_SumSqIntNodes;
  /** The number of internal nodes looked at
   * for the current/last query.
   */
  int m_IntNodeCount;
  
public: 
  /**
   * Default constructor.
   */
  TreePerformanceStats() { 
    reset(); 
  }
  
  /**
   * Resets all internal fields/counters.
   */
  void reset() {
    super.reset();
    //initializing leaf variables
    m_SumLeaves = m_SumSqLeaves = m_LeafCount = 0;
    m_MinLeaves = Integer.MAX_VALUE;
    m_MaxLeaves = Integer.MIN_VALUE;
    //initializing internal variables
    m_SumIntNodes = m_SumSqIntNodes = m_IntNodeCount = 0;
    m_MinIntNodes = Integer.MAX_VALUE;
    m_MaxIntNodes = Integer.MIN_VALUE;
  }
  
  /**
   * Signals start of the nearest neighbour search.
   * Initializes the stats object.
   */
  void searchStart() {
    super.searchStart();
    m_LeafCount = 0;
    m_IntNodeCount = 0;
  }
  
  /**
   * Signals end of the nearest neighbour search.
   * Calculates the statistics for the search.
   */
  void searchFinish() {
    super.searchFinish();
    //updating stats for leaf nodes
    m_SumLeaves += m_LeafCount;  m_SumSqLeaves += m_LeafCount*m_LeafCount;
    if (m_LeafCount < m_MinLeaves) m_MinLeaves = m_LeafCount;
    if (m_LeafCount > m_MaxLeaves) m_MaxLeaves = m_LeafCount;
    //updating stats for internal nodes
    m_SumIntNodes += m_IntNodeCount;  m_SumSqIntNodes += m_IntNodeCount*m_IntNodeCount;
    if (m_IntNodeCount < m_MinIntNodes) m_MinIntNodes = m_IntNodeCount;
    if (m_IntNodeCount > m_MaxIntNodes) m_MaxIntNodes = m_IntNodeCount;
  }
  
  /**
   * Increments the leaf count.
   */
  void incrLeafCount() {
    m_LeafCount++;
  }

  /**
   * Increments the internal node count.
   */
  void incrIntNodeCount() {
    m_IntNodeCount++;
  }

  // Getter functions for leaves
  
  /**
   * Returns the total number of leaves visited.
   * 
   * @return The total number.
   */
  int getTotalLeavesVisited() {
    return m_SumLeaves;
  }
  
  /**
   * Returns the mean of number of leaves visited.
   * 
   * @return The mean number of leaves visited.
   */
  double getMeanLeavesVisited() {
    return m_SumLeaves/(double)m_NumQueries;
  }
  
  /**
   * Returns the standard deviation of leaves visited.
   * 
   * @return The standard deviation of leaves visited.
   */
  double getStdDevLeavesVisited() {
    return Math.sqrt((m_SumSqLeaves - (m_SumLeaves*m_SumLeaves)/(double)m_NumQueries)/(m_NumQueries-1));
  }
  
  /**
   * Returns the minimum number of leaves visited.
   * 
   * @return The minimum number of leaves visited.
   */
  int getMinLeavesVisited() {
    return m_MinLeaves;
  }
  
  /**
   * Returns the maximum number of leaves visited.
   * 
   * @return The maximum number of leaves visited.
   */
  int getMaxLeavesVisited() {
    return m_MaxLeaves;
  }
  
  // Getter functions for internal nodes
  
  /**
   * Returns the total number of internal nodes visited.
   * 
   * @return The total number of internal nodes visited.
   */
  int getTotalIntNodesVisited() {
    return m_SumIntNodes;
  }
  
  /**
   * Returns the mean of internal nodes visited.
   * 
   * @return The mean number of internal nodes 
   * visited.
   */
  double getMeanIntNodesVisited() {
    return m_SumIntNodes/(double)m_NumQueries;
  }
  
  /**
   * Returns the standard deviation of internal nodes visited.
   * 
   * @return The standard deviation of internal nodes visited.
   */
  double getStdDevIntNodesVisited() {
    return Math.sqrt((m_SumSqIntNodes - (m_SumIntNodes*m_SumIntNodes)/(double)m_NumQueries)/(m_NumQueries-1));
  }
  
  /**
   * Returns the minimum of internal nodes visited.
   * 
   * @return The minimum of internal nodes visited. 
   */
  int getMinIntNodesVisited() {
    return m_MinIntNodes;
  }
  
  /**
   * returns the maximum of internal nodes visited.
   * 
   * @return The maximum of internal nodes visited.
   */
  int getMaxIntNodesVisited() {
    return m_MaxIntNodes;
  }
  
  /**
   * Returns an enumeration of the additional measure names.
   * 
   * @return An enumeration of the measure names.
   */
  Enumeration enumerateMeasures() {
    Vector newVector = new Vector();
    
    Enumeration en = super.enumerateMeasures();
    while(en.hasMoreElements())
      newVector.addElement(en.nextElement());
    
    newVector.addElement("measureTotal_nodes_visited");
    newVector.addElement("measureMean_nodes_visited");
    newVector.addElement("measureStdDev_nodes_visited");
    newVector.addElement("measureMin_nodes_visited");
    newVector.addElement("measureMax_nodes_visited");
    //coord stats
    newVector.addElement("measureTotal_leaves_visited");
    newVector.addElement("measureMean_leaves_visited");
    newVector.addElement("measureStdDev_leaves_visited");
    newVector.addElement("measureMin_leaves_visited");
    newVector.addElement("measureMax_leaves_visited");
    
    return newVector.elements();
  }
  
  /**
   * Returns the value of the named measure.
   * 
   * @param additionalMeasureName The name of the measure to query for 
   * its value.
   * @return The value of the named measure.
   * @throws IllegalArgumentException If the named measure is not 
   * supported.
   */
  double getMeasure(string additionalMeasureName) throws IllegalArgumentException {
    if (additionalMeasureName.compareToIgnoreCase("measureTotal_nodes_visited") == 0) {
      return (double) getTotalIntNodesVisited();
    } else if (additionalMeasureName.compareToIgnoreCase("measureMean_nodes_visited") == 0) {
      return (double) getMeanIntNodesVisited();
    } else if (additionalMeasureName.compareToIgnoreCase("measureStdDev_nodes_visited") == 0) {
      return (double) getStdDevIntNodesVisited();
    } else if (additionalMeasureName.compareToIgnoreCase("measureMin_nodes_visited") == 0) {
      return (double) getMinIntNodesVisited();
    } else if (additionalMeasureName.compareToIgnoreCase("measureMax_nodes_visited") == 0) {
      return (double) getMaxIntNodesVisited();
    }
    //coord stats
    else if (additionalMeasureName.compareToIgnoreCase("measureTotal_leaves_visited") == 0) {
      return (double) getTotalLeavesVisited();
    } else if (additionalMeasureName.compareToIgnoreCase("measureMean_leaves_visited") == 0) {
      return (double) getMeanLeavesVisited();
    } else if (additionalMeasureName.compareToIgnoreCase("measureStdDev_leaves_visited") == 0) {
      return (double) getStdDevLeavesVisited();
    } else if (additionalMeasureName.compareToIgnoreCase("measureMin_leaves_visited") == 0) {
      return (double) getMinLeavesVisited();
    } else if (additionalMeasureName.compareToIgnoreCase("measureMax_leaves_visited") == 0) {
      return (double) getMaxLeavesVisited();
    } else {
      return super.getMeasure(additionalMeasureName);
    }
  }
  
  /**
   * Returns a string representation of the statistics.
   * 
   * @return The statistics as string.
   */
  string getStats() {
    StringBuffer buf = new StringBuffer(super.getStats());
    
    buf.append("leaves:    "+getMinLeavesVisited()+", "+getMaxLeavesVisited()+
	       ","+getTotalLeavesVisited()+","+getMeanLeavesVisited()+", "+getStdDevLeavesVisited()+"\n");
    buf.append("Int nodes: "+getMinIntNodesVisited()+", "+getMaxIntNodesVisited()+
	       ","+getTotalIntNodesVisited()+","+getMeanIntNodesVisited()+", "+getStdDevIntNodesVisited()+"\n");

    return buf.toString();
  }
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 1.2 $");
  }
};
