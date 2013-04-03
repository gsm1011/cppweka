#include "AttributeLocator.hpp"

AttributeLocator::AttributeLocator(Instances data, int type) {
    this(data, type, 0, data.numAttributes() - 1);
  }

AttributeLocator::AttributeLocator(Instances data, int type, int fromIndex, int toIndex) {
    super();

    int[] indices = new int[toIndex - fromIndex + 1];
    for (int i = 0; i < indices.length; i++)
      indices[i] = fromIndex + i;

    initialize(data, type, indices);
  }

AttributeLocator::AttributeLocator(Instances data, int type, int[] indices) {
    super();

    initialize(data, type, indices);
  }

void AttributeLocator::initialize(Instances data, int type, int[] indices) {
    m_Data = new Instances(data, 0);
    m_Type = type;

    m_AllowedIndices = new int[indices.length];
    System.arraycopy(indices, 0, m_AllowedIndices, 0, indices.length);

    locate();

    m_Indices        = find(true);
    m_LocatorIndices = find(false);
  }

void AttributeLocator::locate() {
    int         i;

    m_Attributes = new Vector();
    m_Locators   = new Vector();

    for (i = 0; i < m_AllowedIndices.length; i++) {
      if (m_Data.attribute(m_AllowedIndices[i]).type() == Attribute.RELATIONAL)
	m_Locators.add(new AttributeLocator(m_Data.attribute(m_AllowedIndices[i]).relation(), getType()));
      else
	m_Locators.add(NULL);

      if (m_Data.attribute(m_AllowedIndices[i]).type() == getType())
        m_Attributes.add(new Boolean(true));
      else
        m_Attributes.add(new Boolean(false));
    }
  }

vector<int> AttributeLocator::find(bool findAtts) {
    int		i;
    int[]	result;
    Vector	indices;

    // determine locations
    indices = new Vector();
    if (findAtts) {
      for (i = 0; i < m_Attributes.size(); i++) {
	if (((Boolean) m_Attributes.get(i)).boolValue())
	  indices.add(new Integer(i));
      }
    }
    else {
      for (i = 0; i < m_Locators.size(); i++) {
	if (m_Locators.get(i) != NULL)
	  indices.add(new Integer(i));
      }
    }

    // fill array
    result = new int[indices.size()];
    for (i = 0; i < indices.size(); i++)
      result[i] = ((Integer) indices.get(i)).intValue();

    return result;
  }

int AttributeLocator::getActualIndex(int index) {
    return m_AllowedIndices[index];
  }

int AttributeLocator::compareTo(AttributeLocator o) {
    int		result;
    int		i;

    result = 0;

    // 1. check type
    if (this->getType() < o.getType()) {
      result = -1;
    }
    else if (this->getType() > o.getType()) {
      result = 1;
    }
    else {
      // 2. check indices
      if (this->getAllowedIndices().length < o.getAllowedIndices().length) {
	result = -1;
      }
      else if (this->getAllowedIndices().length > o.getAllowedIndices().length) {
	result = 1;
      }
      else {
	for (i = 0; i < this->getAllowedIndices().length; i++) {
	  if (this->getAllowedIndices()[i] < o.getAllowedIndices()[i]) {
	    result = -1;
	    break;
	  }
	  else if (this->getAllowedIndices()[i] > o.getAllowedIndices()[i]) {
	    result = 1;
	    break;
	  }
	  else {
	    result = 0;
	  }
	}
      }
    }

    return result;
  }
