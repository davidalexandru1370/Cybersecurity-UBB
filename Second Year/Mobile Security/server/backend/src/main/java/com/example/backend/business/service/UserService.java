package com.example.backend.business.service;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.security.crypto.bcrypt.BCryptPasswordEncoder;
import org.springframework.stereotype.Service;

import com.example.backend.business.entities.CreateUserDTO;
import com.example.backend.business.repository.UserRepository;
import com.example.backend.business.service.interfaces.IUserService;
import com.example.backend.core.domain.User;
import com.example.backend.core.exceptions.ExistingAccountException;

@Service
public class UserService implements IUserService {

    @Autowired
    private UserRepository userRepository;

    @Autowired
    private BCryptPasswordEncoder passwordEncoder;

    @Override
    public User createUser(CreateUserDTO createUserDTO) throws ExistingAccountException {
        var existingUser = userRepository.findByEmail(createUserDTO.getEmail());

        if (existingUser != null) {
            throw new ExistingAccountException("User with email " + createUserDTO.getEmail() + " already exists.");
        }

        var encryptedPassword = passwordEncoder.encode(createUserDTO.getPassword());
        User newUser = new User(createUserDTO.getEmail(), encryptedPassword, createUserDTO.getRole());

        return userRepository.save(newUser);
    }

    @Override
    public User getUserByEmail(String email) {
        return userRepository.findByEmail(email);
    }

    @Override
    public boolean validateUserCredentials(String email, String password) {
        User user = userRepository.findByEmail(email);
        var encryptedPassword = passwordEncoder.encode(password);
        if (user != null && user.getPassword().equals(encryptedPassword)) {
            return true;
        }
        return false;
    }
}
