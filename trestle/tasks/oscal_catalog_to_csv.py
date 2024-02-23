# -*- mode:python; coding:utf-8 -*-
# Copyright (c) 2023 IBM Corp. All rights reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
"""OSCAL transformation tasks."""

# mypy: ignore-errors  # noqa E800
import configparser
import copy
import csv
import datetime
import logging
import pathlib
import re
import traceback
from typing import Iterator, List, Optional

from trestle.core.catalog.catalog_interface import CatalogInterface, ControlInterface
from trestle.oscal.catalog import Catalog
from trestle.oscal.catalog import Control
from trestle.oscal.common import HowMany
from trestle.oscal.common import Link
from trestle.oscal.common import Parameter
from trestle.oscal.common import Part
from trestle.tasks.base_task import TaskBase
from trestle.tasks.base_task import TaskOutcome

logger = logging.getLogger(__name__)

timestamp = datetime.datetime.utcnow().replace(microsecond=0).replace(tzinfo=datetime.timezone.utc).isoformat()

recurse = True

level_control = 'control'
level_statement = 'statement'
level_default = level_statement
level_list = [level_control, level_statement]
params_default = True
param_ids_default = False
params_file_default = None
verbose_csv_default = False


def join_str(s1: Optional[str], s2: Optional[str], sep: str = ' ') -> Optional[str]:
    """Join strings."""
    if s1 is None:
        rval = s2
    elif s2 is None:
        rval = s1
    else:
        rval = f'{s1}{sep}{s2}'
    return rval


def convert_control_id(control_id: str) -> str:
    """Convert control id."""
    rval = copy.copy(control_id)
    rval = rval.upper()
    if '.' in rval:
        rval = rval.replace('.', '(')
        rval = rval + ')'
    return rval


def convert_smt_id(smt_id: str) -> str:
    """Convert smt id."""
    parts = smt_id.split('_smt')
    seg1 = convert_control_id(parts[0])
    seg2 = ''
    if len(parts) == 2:
        seg2 = parts[1]
        if '.' in seg2:
            seg2 = seg2.replace('.', '(')
            seg2 = seg2 + ')'
    rval = f'{seg1}{seg2}'
    return rval


class CsvHelper:
    """Csv Helper."""

    def __init__(self, path) -> None:
        """Initialize."""
        self.path = path

    def write(self, rows: List[List[str]]) -> None:
        """Write csv file."""
        with open(self.path, 'w', newline='', encoding='utf-8') as output:
            csv_writer = csv.writer(output, delimiter=',', quotechar='"', quoting=csv.QUOTE_MINIMAL)
            for row in rows:
                csv_writer.writerow(row)


class CatalogHelper:
    """OSCAL Catalog Helper."""

    def __init__(self, path, resolve_parms=params_default, verbose_csv=verbose_csv_default, param_ids=param_ids_default) -> None:
        """Initialize."""
        self.path = path
        self.catalog = Catalog.oscal_read(path)
        self.catalog_interface = CatalogInterface(self.catalog)
        self._init_control_parent_map()
        self.resolve_parms = resolve_parms
        self.parameters = {}
        self.verbose_csv = verbose_csv
        self.param_ids = param_ids

    def _init_control_parent_map(self, recurse=True) -> None:
        """Initialize map: Child Control.id to parent Control."""
        self._control_parent_map = {}
        for control in self.catalog_interface.get_all_controls_from_catalog(recurse):
            parents = self.catalog_interface.get_dependent_control_ids(control.id)
            for parent in parents:
                # assert child has only one parent
                if parent in self._control_parent_map.keys():
                    raise RuntimeError('{parent} duplicate?')
                self._control_parent_map[parent] = control

    def get_parent_control(self, ctl_id: str) -> Control:
        """Return parent Control of child Control.id, if any."""
        return self._control_parent_map.get(ctl_id)

    def get_family_controls(self, ctl_id: str) -> List[Control]:
        """Return family of controls for Control.id, if any."""
        rval = []
        search_id = ctl_id.split('.')[0]
        for control in self.catalog_interface.get_all_controls_from_catalog(recurse):
            if control.id.startswith(search_id):
                rval.append(control)
        return rval

    def get_controls(self, recurse=True) -> Iterator:
        """Return controls iterator."""
        for control in self.catalog_interface.get_all_controls_from_catalog(recurse):
            yield control

    def get_statement_text_for_control(self, control: Control) -> Optional[str]:
        """Get statement text for control."""
        statement_text = self._withdrawn(control)
        return statement_text

    def get_statement_text_for_part(self, control: Control, part: Part) -> Optional[str]:
        """Get statement text for part."""
        statement_text, params = self._derive_text(control, part)
        if part.parts:
            for subpart in part.parts:
                if '_smt' in subpart.id:
                    partial_text, partial_params = self._derive_text(control, subpart)
                    statement_text = join_str(statement_text, partial_text)
                    params = {**params, **partial_params}
        return statement_text, params

    def _withdrawn(self, control: Control) -> Optional[str]:
        """Check if withdrawn."""
        rval = None
        for prop in control.props:
            if prop.name.lower() == 'status' and prop.value.lower() == 'withdrawn':
                status = self._get_status(control)
                rval = join_str('Withdrawn', status, '')
                rval = f'[{rval}]'
                break
        return rval

    def _link_generator(self, control: Control) -> Iterator[Link]:
        """Link generator."""
        if control.links:
            for link in control.links:
                yield link

    def _get_status(self, control: Control) -> Optional[str]:
        """Get status."""
        rval = None
        ilist = None
        for link in self._link_generator(control):
            if link.rel.lower() == 'moved-to':
                moved = self._href_to_control(link.href)
                rval = f': Moved to {moved}.'
                break
            if link.rel.lower() == 'incorporated-into':
                incorporated = self._href_to_control(link.href)
                if ilist is None:
                    ilist = f'{incorporated}'
                else:
                    ilist = f'{ilist}, {incorporated}'
        if ilist:
            rval = f': Incorporated into {ilist}.'
        return rval

    def _href_to_control(self, href: str) -> str:
        """Convert href to control."""
        rval = href.replace('#', '').upper()
        return rval

    def _derive_text(self, control: Control, part: Part) -> Optional[str]:
        """Derive control text."""
        rval = None
        params = {}
        if part.prose:
            id_ = self._derive_id(part.id)
            text, params = self._resolve_parms(control, part.prose)
            if not self.verbose_csv:
                rval = join_str(id_, text)
            else:
                rval = text
        return rval, params

    def _derive_id(self, id_: str) -> str:
        """Derive control text sub-part id."""
        rval = None
        id_parts = id_.split('_smt')
        if id_parts[1]:
            id_sub_parts = id_parts[1].split('.')
            if len(id_sub_parts) == 2:
                rval = f'{id_sub_parts[1]}.'
            elif len(id_sub_parts) == 3:
                rval = f'{id_sub_parts[2]}.'
            elif len(id_sub_parts) == 4:
                rval = f'({id_sub_parts[3]})'
        return rval

    def _resolve_parms(self, control: Control, utext: str) -> str:
        """Resolve parm."""
        rtext, params = self._resolve_parms_for_control(control, utext)
        if '{{' in rtext:
            parent_control = self.get_parent_control(control.id)
            if parent_control:
                rtext, params = self._resolve_parms_for_control(parent_control, rtext)
        if '{{' in rtext:
            family_controls = self.get_family_controls(control.id)
            for family_control in family_controls:
                rtext, params = self._resolve_parms_for_control(family_control, rtext)
        if '{{' in rtext:
            text = f'control.id: {control.id} unresolved: {rtext}'
            raise RuntimeError(text)
        return rtext, params

    def _resolve_parms_for_control(self, control: Control, utext: str) -> str:
        """Resolve parms for control."""
        rtext = utext
        staches: List[str] = re.findall(r'{{.*?}}', utext)
        params = {}
        if staches:
            for stach in staches:
                parm_id = stach
                parm_id = parm_id.replace('{{', '')
                parm_id = parm_id.replace('}}', '')
                parm_id = parm_id.split(',')[1].strip()
                value, returned_params = self._get_parm_value(control, parm_id)
                params = {**params, **returned_params}
                if value:
                    if self.resolve_parms:
                        if self.param_ids:
                            rtext = rtext.replace(stach, f'[{parm_id}]: {value}')
                        else:
                            rtext = rtext.replace(stach, value)
                    else:
                        rtext = rtext.replace(stach, f'[{parm_id}]')
                        params[parm_id] = value
        return rtext, params

    def _get_parm_value(self, control: Control, parm_id: str) -> str:
        """Get parm value."""
        rval = None
        params = {}
        if control.params:
            for param in control.params:
                if param.id != parm_id:
                    continue
                if param.label:
                    rval = f'[Assignment: {param.label}]'
                elif param.select:
                    choices, params = self._get_parm_choices(control, param)
                    if param.select.how_many == HowMany.one:
                        rval = f'[Selection (one): {choices}]'
                    else:
                        rval = f'[Selection (one or more): {choices}]'
                    break
        return rval, params

    def _get_parm_choices(self, control: Control, param: Parameter) -> str:
        """Get parm choices."""
        choices = ''
        params = {}
        for choice in param.select.choice:
            rchoice, rparams = self._resolve_parms(control, choice)
            params = {**params, **rparams}
            if choices:
                choices += f'; {rchoice}'
            else:
                choices += f'{rchoice}'
        return choices, params


class ContentManager():
    """Content manager."""

    def __init__(self, catalog_helper: CatalogHelper, resolve_parms=params_default, verbose_csv=verbose_csv_default) -> None:
        """Initialize."""
        self.catalog_helper = catalog_helper
        self.rows = []
        self.parameters = {}
        self.row_template = None
        self.resolve_parms = resolve_parms
        self.verbose_csv = verbose_csv
        self.control_interface = ControlInterface()

    def add(self, row: List):
        """Add row."""
        n_row = copy.copy(row)
        t_row = self.row_template
        if t_row:
            for index in range(3):
                if n_row[index] == t_row[index]:
                    if not self.verbose_csv:
                        n_row[index] = None
        self.rows.append(n_row)
        self.row_template = row

    def add_params(self, params: dict):
        """Add params."""
        for key in params:
            self.parameters[key] = params[key]

    def get_content(self, level: str) -> List:
        """Get content."""
        if level == level_control:
            rval = self._get_content_by_control()
        else:
            rval = self._get_content_by_statement()
        return rval

    def get_params(self) -> List:
        """Return parameters dict as list of lists."""
        params = [['Parameter ID', 'Value']]
        for k, v in sorted(self.parameters.items()):
            params.append([k, v])
        return params

    def _get_content_by_statement(self) -> List:
        """Get content by statement."""
        catalog_helper = self.catalog_helper
        if self.verbose_csv:
            header = ['Sort ID', 'Control Family', 'Control Identifier', 'Control Title', 'Statement Identifier', 'Statement Text']
        else:
            header = ['Control Identifier', 'Control Title', 'Statement Identifier', 'Statement Text']

        if not self.resolve_parms:
            header.append('Parameters')
        self.rows.append(header)
        for control in catalog_helper.get_controls():
            if control.parts:
                self._add_parts_by_statement(control)
            else:
                statement_text = catalog_helper.get_statement_text_for_control(control)
                if self.verbose_csv:
                    sort_id = convert_control_id(self.control_interface.get_sort_id(control))
                    control_id = convert_control_id(control.id)
                    family = self._get_family(control)
                    row = [sort_id, family, control_id, control.title, '', statement_text]
                else:
                    control_id = convert_control_id(control.id)
                    row = [control_id, control.title, '', statement_text]
                if not self.resolve_parms:
                    self.add_params(params)
                    params_text = ', '.join(f'{k}: {v}' for k, v in sorted(params.items()))
                    row.append(params_text)
                self.add(row)
        return self.rows

    def _add_subparts_by_statement(self, control: Control, part: Part) -> None:
        """Add subparts by statement."""
        catalog_helper = self.catalog_helper
        for subpart in part.parts:
            if '_smt' in subpart.id:
                statement_text, params = catalog_helper.get_statement_text_for_part(control, subpart)
                if self.verbose_csv:
                    family = self._get_family(control)
                    sort_id = convert_control_id(self.control_interface.get_sort_id(control))
                    control_id = convert_control_id(control.id)
                    row = [sort_id, family, control_id, control.title, convert_smt_id(subpart.id), statement_text]
                else:
                    control_id = convert_control_id(control.id)
                    row = [control_id, control.title, convert_smt_id(subpart.id), statement_text]

                if not self.resolve_parms:
                    self.add_params(params)
                    params_text = ', '.join(f'{k}: {v}' for k, v in sorted(params.items()))
                    row.append(params_text)
                self.add(row)

    def _add_parts_by_statement(self, control: Control) -> None:
        """Add parts by statement."""
        catalog_helper = self.catalog_helper
        for part in control.parts:
            if part.id:
                if '_smt' not in part.id:
                    continue
                if part.parts:
                    self._add_subparts_by_statement(control, part)
                else:
                    statement_text, params = catalog_helper.get_statement_text_for_part(control, part)
                    if self.verbose_csv:
                        family = self._get_family(control)
                        sort_id = convert_control_id(self.control_interface.get_sort_id(control))
                        control_id = convert_control_id(control.id)
                        row = [sort_id, family, control_id, control.title, convert_smt_id(part.id), statement_text]
                    else:
                        control_id = convert_control_id(control.id)
                        row = [control_id, control.title, convert_smt_id(part.id), statement_text]
                    if not self.resolve_parms:
                        self.add_params(params)
                        params_text = ', '.join(f'{k}: {v}' for k, v in sorted(params.items()))
                        row.append(params_text)
                    self.add(row)

    def _get_content_by_control(self) -> List:
        """Get content by statement."""
        catalog_helper = self.catalog_helper
        header = ['Control Identifier', 'Control Title', 'Control Text']
        self.rows.append(header)
        for control in catalog_helper.get_controls():
            if self.verbose_csv:
                control_id = convert_control_id(self.control_interface.get_sort_id(control))
            else:
                control_id = convert_control_id(control.id)
            if control.parts:
                self._add_parts_by_control(control)
            else:
                control_text = catalog_helper.get_statement_text_for_control(control)
                if self.resolve_parms:
                    row = [control_id, control.title, control_text]
                else:
                    self.add_params(params)
                    params_text = ', '.join(f'{k}: {v}' for k, v in sorted(params.items()))
                    row = [control_id, control.title, control_text, params_text]
                self.add(row)
        return self.rows

    def _add_subparts_by_control(self, control: Control, part: Part, control_text) -> str:
        """Add subparts by control."""
        catalog_helper = self.catalog_helper
        for subpart in part.parts:
            if '_smt' in subpart.id:
                statement_text, params = catalog_helper.get_statement_text_for_part(control, subpart)
                control_text = join_str(control_text, statement_text)
        return control_text, params

    def _add_parts_by_control(self, control: Control) -> None:
        """Add parts by control."""
        catalog_helper = self.catalog_helper
        control_id = convert_control_id(control.id)
        control_text = None
        for part in control.parts:
            if part.id:
                if '_smt' not in part.id:
                    continue
                if part.parts:
                    control_text, params = self._add_subparts_by_control(control, part, control_text)
                else:
                    statement_text, params = catalog_helper.get_statement_text_for_part(control, part)
                    control_text = join_str(control_text, statement_text)
        row = [control_id, control.title, control_text]
        self.add(row)

    def _get_family(self, control: Control) -> str:
        family = self.catalog_helper.catalog_interface.get_group_info_by_control(control.id)
        rval = ''
        if family is not None and len(family) > 1:
            rval = f'{family[1]} ({family[0].upper()})'
        return rval


class OscalCatalogToCsv(TaskBase):
    """
    Task to transform OSCAL catalog to .csv.

    Attributes:
        name: Name of the task.
    """

    name = 'oscal-catalog-to-csv'

    def __init__(self, config_object: Optional[configparser.SectionProxy]) -> None:
        """
        Initialize trestle task.

        Args:
            config_object: Config section associated with the task.
        """
        super().__init__(config_object)

    def print_info(self) -> None:
        """Print the help string."""
        logger.info(f'Help information for {self.name} task.')
        logger.info('')
        logger.info('Purpose: Create .csv from OSCAL catalog.')
        logger.info('')
        logger.info('Configuration flags sit under [task.oscal-catalog-to-csv]:')
        text1 = '  input-file             = '
        text2 = '(required) path of file to read the catalog.'
        logger.info(text1 + text2)
        text1 = '  output-dir             = '
        text2 = '(required) path of directory to write the generated .csv file.'
        logger.info(text1 + text2)
        text1 = '  output-name            = '
        text2 = '(optional) name of the generated .csv file [default is name of input file with .csv suffix].'
        logger.info(text1 + text2)
        text1 = '  output-overwrite       = '
        text2 = '(optional) true [default] or false; replace existing output when true.'
        logger.info(text1 + text2)
        text1 = '  resolve-param          = '
        text2 = f'(optional) one of: {True} [default] or {False} resolve parameters into control prose.'
        logger.info(text1 + text2)
        text1 = '  param-ids          = '
        text2 = f'(optional) one of: {True} or {False} [default] always show param ids in control prose (redundant'
        text3 = f' if resolve-param = {False}).'
        logger.info(text1 + text2 + text3)
        text1 = '  params-file            = '
        text2 = f'(optional) filename to write parameters as csv, in output-dir. Requires resolve-param = {True}.'
        logger.info(text1 + text2)
        text1 = '  level                  = '
        text2 = f'(optional) one of: {level_control} or {level_statement} [default].'
        logger.info(text1 + text2)
        text1 = '  verbose-csv            = '
        text2 = f'(optional) one of: {True} or {False} [default] output more control metadata to csv.'
        logger.info(text1 + text2)

    def simulate(self) -> TaskOutcome:
        """Provide a simulated outcome."""
        return TaskOutcome('simulated-success')

    def execute(self) -> TaskOutcome:
        """Provide an actual outcome."""
        try:
            return self._execute()
        except Exception:
            logger.info(traceback.format_exc())
            return TaskOutcome('failure')

    def _execute(self) -> TaskOutcome:
        """Wrap the execute for exception handling."""
        # config processing
        if not self._config:
            logger.warning('config missing')
            return TaskOutcome('failure')
        # input
        ifile = self._config.get('input-file')
        if not ifile:
            logger.warning('input-file missing')
            return TaskOutcome('failure')
        ipth = pathlib.Path(ifile)
        # overwrite
        self._overwrite = self._config.getboolean('output-overwrite', True)
        # output
        odir = self._config.get('output-dir')
        if not odir:
            logger.warning('output-dir missing')
            return TaskOutcome('failure')
        opth = pathlib.Path(odir)
        opth.mkdir(exist_ok=True, parents=True)
        iname = ipth.name.split('.')[0]
        oname = self._config.get('output-name', f'{iname}.csv')
        ofpth = opth / oname
        if not self._overwrite and ofpth.exists():
            logger.warning(f'output catalog: {ofpth} already exists')
            return TaskOutcome('failure')
        csv_helper = CsvHelper(ofpth)
        # level
        level = self._config.get('level', level_default)
        if level not in level_list:
            logger.warning(f'level: {level} unknown')
            return TaskOutcome('failure')
        # params
        resolve_parms = self._config.getboolean('resolve-params', params_default)
        param_ids = self._config.getboolean('param-ids', param_ids_default)
        print(f'param_ids: {param_ids}')
        params_file = self._config.get('params-file', params_file_default)
        # verbose-csv
        verbose_csv = self._config.getboolean('verbose-csv', verbose_csv_default)
        # helper
        catalog_helper = CatalogHelper(ipth, resolve_parms, verbose_csv, param_ids)
        # process
        content_manager = ContentManager(catalog_helper, resolve_parms, verbose_csv)
        rows = content_manager.get_content(level)
        # write catalog
        csv_helper.write(rows)
        logger.info(f'output-file: {ofpth}')
        # write params
        if params_file:
            if resolve_parms:
                logger.warning('resolve-params = false must be specified to write parameters file')
                return TaskOutcome('failure')
            ofpth = opth / params_file
            if not self._overwrite and ofpth.exists():
                logger.warning(f'output params: {ofpth} already exists')
                return TaskOutcome('failure')
            csv_helper = CsvHelper(ofpth)
            csv_helper.write(content_manager.get_params())

        # success
        return TaskOutcome('success')
