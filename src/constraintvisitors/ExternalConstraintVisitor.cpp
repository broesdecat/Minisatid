#include "external/ConstraintAdditionInterface.hpp"
#include "space/Remapper.hpp"
#include "external/Translator.hpp"

using namespace std;
using namespace MinisatID;

ExternalConstraintVisitor::ExternalConstraintVisitor(const SolverOption& options, const std::string& name) :
		ConstraintVisitor(name), basicoptions(options), remapper(new Remapper()), _translator(new PlainTranslator()) {
	_origremapper = remapper;
	_origtranslator = _translator;
}
ExternalConstraintVisitor::ExternalConstraintVisitor(Remapper* remapper, Translator *translator, const SolverOption& options, const std::string& name) :
		ConstraintVisitor(name), basicoptions(options), remapper(remapper), _origremapper(NULL), _translator(translator), _origtranslator(NULL) {
}

ExternalConstraintVisitor::~ExternalConstraintVisitor() {
	if(_origremapper!=NULL){
		delete (_origremapper);
	}
	if(_origtranslator!=NULL){
		delete (_origtranslator);
	}
}
void ExternalConstraintVisitor::notifyFinishParsing() {
	getTranslator()->finish();
}

std::string ExternalConstraintVisitor::toString(uint id) const {
	std::stringstream ss;
	if (getRemapper()->wasInput(id)) {
		auto origid = getRemapper()->getOrigID(id);
		ss <<origid;
		return ss.str();
		/*if (getTranslator()->hasTranslation(origid)) { TODO var to translated string
			ss << getTranslator()->toString(origid);
			return ss.str();
		}*/
	}
	ss << "internvar_" << id;
	return ss.str();
}
std::string ExternalConstraintVisitor::toString(const Lit& l) const {
	std::stringstream ss;
	if (getRemapper()->wasInput(l)) {
		auto lit = getRemapper()->getLiteral(l);
		if (getTranslator()->hasTranslation(lit)) {
			ss << getTranslator()->toString(lit);
			return ss.str();
		}
	}
	ss << (sign(l) ? "-" : "") << "internal_" << var(l) + 1; // NOTE: do not call <<l, this will cause an infinite loop (as that calls this method!)
	return ss.str();
}
std::string ExternalConstraintVisitor::toString(const litlist& literals) const {
	std::stringstream ss;
	bool begin = true;
	for (auto i = literals.cbegin(); i < literals.cend(); ++i) {
		if (not begin) {
			ss << " | ";
		}
		begin = false;
		ss << toString(*i);
	}
	return ss.str();
}
