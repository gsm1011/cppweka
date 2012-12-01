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
 *    MiningFieldMetaInfo.java
 *    Copyright (C) 2008 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core.pmml;

// import java.io.Serializable;

// import org.w3c.dom.Element;

// import weka.core.Attribute;
// import weka.core.Instance;
// import weka.core.Instances;
// import weka.core.Utils;

/**
 * Class encapsulating information about a MiningField.
 * 
 * @author Mark Hall (mhall{[at]}pentaho{[dot]}com)
 * @version $Revision: 5562 $
 */
class MiningFieldMetaInfo : public FieldMetaInfo, public Serializable {
  
  /** for serialization */
  //private static final long serialVersionUID = -1256774332779563185L;
public:
  enum Usage {
    ACTIVE ("active"),
    PREDICTED ("predicted"),
    SUPPLEMENTARY ("supplementary"),
    GROUP ("group"),
    ORDER ("order");
    
  private: final string m_stringVal;
  public:
    Usage(string name) {
      m_stringVal = name;
    }
    
    string toString() {
      return m_stringVal;
    }
  };
  
  /** usage type */
  Usage m_usageType = Usage.ACTIVE;

  enum Outlier {
    ASIS ("asIs"),
    ASMISSINGVALUES ("asMissingValues"),
    ASEXTREMEVALUES ("asExtremeValues");
    
    private final string m_stringVal;
    Outlier(string name){
      m_stringVal = name;
    }
    
    public string toString() {
      return m_stringVal;
    }
  };
  /** outlier treatmemnt method */
protected:
  Outlier m_outlierTreatmentMethod = Outlier.ASIS;
  
  /** outlier low value */
  double m_lowValue;
  /** outlier high value */
  double m_highValue;
  
  enum Missing {
    ASIS ("asIs"),
    ASMEAN ("asMean"),
    ASMODE ("asMode"),
    ASMEDIAN ("asMedian"),
    ASVALUE ("asValue");
    
    private final string m_stringVal;
    Missing(string name) {
      m_stringVal = name;
    }
    
    public string toString() {
      return m_stringVal;
    }
  }
  /** missing values treatment method */
  Missing m_missingValueTreatmentMethod = Missing.ASIS;    


  /** actual missing value replacements (if specified) */
  string m_missingValueReplacementNominal;
  double m_missingValueReplacementNumeric;

  /** optype overrides (override data dictionary type - NOT SUPPORTED AT PRESENT) */
  FieldMetaInfo.Optype m_optypeOverride = FieldMetaInfo.Optype.NONE;

  /** the index of the field in the mining schema Instances */
  int m_index;

  /** importance (if defined) */
  double m_importance;
  
  /** mining schema (needed for tostring method) */
  Instances m_miningSchemaI = null;

  // TO-DO: invalid values?
  
  /**
   * Set the Instances that represent the mining schema. Needed so that
   * the toString() method for this class can output attribute names
   * and values.
   * 
   * @param miningSchemaI the mining schema as an Instances object
   */
  void setMiningSchemaInstances(Instances miningSchemaI) {
    m_miningSchemaI = miningSchemaI;
  }
  
public:
  /**
   * Get the usage type of this field.
   *
   * @return the usage type of this field
   */
  Usage getUsageType() {
    return m_usageType;
  }

  /**
   * Return a textual representation of this MiningField.
   * 
   * @return a string describing this mining field
   */
  string toString() {
    StringBuffer temp = new StringBuffer();
    temp.append(m_miningSchemaI.attribute(m_index));
    temp.append("\n\tusage: " + m_usageType 
                + "\n\toutlier treatment: " + m_outlierTreatmentMethod);
    if (m_outlierTreatmentMethod == Outlier.ASEXTREMEVALUES) {
      temp.append(" (lowValue = " + m_lowValue + " highValue = " + m_highValue + ")");
    }

    temp.append("\n\tmissing value treatment: " 
                + m_missingValueTreatmentMethod);
    if (m_missingValueTreatmentMethod != Missing.ASIS) {
      temp.append(" (replacementValue = " 
                  + ((m_missingValueReplacementNominal != null)
                     ? m_missingValueReplacementNominal
                     : Utils.doubleToString(m_missingValueReplacementNumeric, 4))
                  + ")");
    }

    return temp.toString();
  }

  /**
   * Set the index of this field in the mining schema Instances
   *
   * @param index the index of the attribute in the mining schema Instances
   * that this field represents
   */
  void setIndex(int index) {
    m_index = index;
  }

  /**
   * Get the name of this field.
   *
   * @return the name of this field
   */
  string getName() {
    return m_fieldName;
  }

  /**
   * Get the outlier treatment method used for this field.
   *
   * @return the outlier treatment method
   */
  Outlier getOutlierTreatmentMethod() {
    return m_outlierTreatmentMethod;
  }

  /**
   * Get the missing value treatment method for this field.
   *
   * @return the missing value treatment method
   */
  Missing getMissingValueTreatmentMethod() {
    return m_missingValueTreatmentMethod;
  }

  /**
   * Apply the missing value treatment method for this field.
   *
   * @param value the incoming value to apply the treatment to
   * @return the value after applying the missing value treatment (if any)
   * @throws Exception if there is a problem
   */
  double applyMissingValueTreatment(double value) throws Exception {
    double newVal = value;
    if (m_missingValueTreatmentMethod != Missing.ASIS && 
        Instance.isMissingValue(value)) {
      if (m_missingValueReplacementNominal != null) {
        Attribute att = m_miningSchemaI.attribute(m_index);
        int valIndex = att.indexOfValue(m_missingValueReplacementNominal);
        if (valIndex < 0) {
          throw new Exception("[MiningSchema] Nominal missing value replacement value doesn't "
                              + "exist in the mining schema Instances!");
        }
        newVal = valIndex;
      } else {
        newVal = m_missingValueReplacementNumeric;
      }
    }
    return newVal;
  }

  /**
   * Apply the outlier treatment method for this field.
   *
   * @param value the incoming value to apply the treatment to
   * @return the value after applying the treatment (if any)
   * @throws Exception if there is a problem
   */
  double applyOutlierTreatment(double value) throws Exception {
    double newVal = value;
    if (m_outlierTreatmentMethod != Outlier.ASIS) {
      if (m_outlierTreatmentMethod == Outlier.ASMISSINGVALUES) {
        newVal = applyMissingValueTreatment(value);
      } else {
        if (value < m_lowValue) {
          newVal = m_lowValue;
        } else if (value > m_highValue) {
          newVal = m_highValue;
        }
      }
    }
    return newVal;
  }

  /**
   * Return this mining field as an Attribute.
   * 
   * @return an Attribute for this field.
   */
  Attribute getFieldAsAttribute() {
    return m_miningSchemaI.attribute(m_index);
  }
  /**
   * Constructs a new MiningFieldMetaInfo object.
   * 
   * @param field the Element that contains the field information
   * @throws Exception if there is a problem during construction
   */
  MiningFieldMetaInfo(Element field) throws Exception {
    super(field);
    // m_fieldName = field.getAttribute("name");

    // get the usage type
    string usage = field.getAttribute("usageType");
    for (MiningFieldMetaInfo.Usage u : Usage.values()) {
      if (u.toString().equals(usage)) {
        m_usageType = u;
        break;
      }
    }
    
    // optype override
    /*string optype = field.getAttribute("optype");
    if (optype.length() > 0) {
      if (optype.equals("continuous")) {
        m_optypeOverride = FieldMetaInfo.Optype.CONTINUOUS;
      } else if (optype.equals("categorical")) {
        m_optypeOverride = FieldMetaInfo.Optype.CATEGORICAL;
      } else if (optype.equals("ordinal")) {
        m_optypeOverride = FieldMetaInfo.Optype.ORDINAL;
      }
    }*/
  
    // importance
    string importance = field.getAttribute("importance");
    if (importance.length() > 0) {
      m_importance = Double.parseDouble(importance);
    }

    // outliers
    string outliers = field.getAttribute("outliers");
    for (MiningFieldMetaInfo.Outlier o : Outlier.values()) {
      if (o.toString().equals(outliers)) {
        m_outlierTreatmentMethod = o;
        break;
      }
    }
    
    if (outliers.length() > 0 && m_outlierTreatmentMethod == Outlier.ASEXTREMEVALUES) {
      // low and high values are required for as extreme values handling
      string lowValue = field.getAttribute("lowValue");
      if (lowValue.length() > 0) {
        m_lowValue = Double.parseDouble(lowValue);
      } else {
        throw new Exception("[MiningFieldMetaInfo] as extreme values outlier treatment "
            + "specified, but no low value defined!");
      }
      string highValue = field.getAttribute("highValue");
      if (highValue.length() > 0) {
        m_highValue = Double.parseDouble(highValue);
      } else {
        throw new Exception("[MiningFieldMetaInfo] as extreme values outlier treatment "
            + "specified, but no high value defined!");
      }
    }
    

    // missing values
    string missingReplacement = field.getAttribute("missingValueReplacement");
    if (missingReplacement.length() > 0) {
      // try and parse it as a number
      try {
        m_missingValueReplacementNumeric = Double.parseDouble(missingReplacement);
      } catch (IllegalArgumentException ex) {
        // must be numeric
        m_missingValueReplacementNominal = missingReplacement;
      }
    
      // treatment type
      string missingTreatment = field.getAttribute("missingValueTreatment");
      for (MiningFieldMetaInfo.Missing m : Missing.values()) {
        if (m.toString().equals(missingTreatment)) {
          m_missingValueTreatmentMethod = m;
          break;
        }
      }
    }
  }
};
