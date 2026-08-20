import importedBind from "./ok.js"

function okRead() {
    return importedBind
}

function case_import_assign() {
    importedBind = 1 // want "assigning to an imported binding"
}
