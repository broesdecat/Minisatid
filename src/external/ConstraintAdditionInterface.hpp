/************************************
 ConstraintAdditionInterface.hpp
 this file belongs to GidL 2.0
 (c) K.U.Leuven
 ************************************/

#ifndef CONSTRAINTADDITIONINTERFACE_HPP_
#define CONSTRAINTADDITIONINTERFACE_HPP_

namespace MinisatID {

class Remapper;

template<class Engine>
class ConstraintAdditionInterface {
protected:
	Remapper* remapper;
public:
	ConstraintAdditionInterface() :
			remapper(new Remapper()) {
	}
	virtual ~ConstraintAdditionInterface() {
		delete (remapper);
	}

	Remapper& getRemapper() const {
		return *remapper;
	}
	virtual Engine* getEngine() const = 0;
};
}

#endif /* CONSTRAINTADDITIONINTERFACE_HPP_ */
