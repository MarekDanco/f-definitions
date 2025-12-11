"""Module for testing ReqPivot condition"""


class ReqPivot:
    def __init__(self, formula):
        self.formula = formula
        self.max_entity = None
        self.min_entity = None

    def _get_entities(self):
        pass

    def test(self):
        entities = self._get_entities()
        return False
