const Button = () => (
  <button onClick={this.handleClick.bind(this)} />  // want ".bind() in JSX"
);

const Ok = ({ onClick }) => <button onClick={onClick} />;
