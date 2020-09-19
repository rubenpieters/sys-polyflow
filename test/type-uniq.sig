sig type-uniq.

kind    tm, ty     type.

type    i          ty.
type    arrow      ty -> ty -> ty.

type    app        tm -> tm -> tm.
type    abs        ty -> (tm -> tm) -> tm.

type    of         tm -> ty -> o.
